import argparse
import bz2
import getpass
import gzip
import hashlib
import lzma
import os
import struct
from pathlib import Path

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from PIL import Image

try:
    from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
except ImportError:
    Argon2id = None

SALT_SIZE = 16
NONCE_SIZE = 12
KEY_SIZE = 32
GROUP_ID_SIZE = 8
MAX_SHARDS = 65535
MAGIC_ARGON2 = b"SGA2"
MAGIC_PBKDF2 = b"SGP2"
MAGIC_ARGON2_V3 = b"SGA3"
MAGIC_PBKDF2_V3 = b"SGP3"
V2_MAGIC_SET = (MAGIC_ARGON2, MAGIC_PBKDF2)
V3_MAGIC_SET = (MAGIC_ARGON2_V3, MAGIC_PBKDF2_V3)
MAGIC_SET = V2_MAGIC_SET + V3_MAGIC_SET
LEGACY_HEADER = struct.Struct(">4s16s12sIB")
SHARD_HEADER = struct.Struct(">4s16s12s8sIIIBHH")
HEADER_SIZE_V2 = LEGACY_HEADER.size
HEADER_SIZE_V3 = SHARD_HEADER.size
HEADER_BITS_V2 = HEADER_SIZE_V2 * 8
HEADER_BITS_V3 = HEADER_SIZE_V3 * 8
BOOT_DOMAIN = b"stego-boot-v2"
PBKDF2_ITERATIONS = 600_000
ARGON2_MEMORY_KIB = 65536
ARGON2_ITERATIONS = 2
ARGON2_LANES = 1
GCM_OVERHEAD = 1 + 4 + 16
CODEC_IDS = {"none": 0, "gzip": 1, "bzip2": 2, "xz": 3}
ID_CODECS = {value: key for key, value in CODEC_IDS.items()}


def iter_bits(data):
    for byte in data:
        for shift in range(7, -1, -1):
            yield (byte >> shift) & 1


def pack_values(data, bits):
    values = []
    acc = 0
    acc_bits = 0
    mask = (1 << bits) - 1
    for byte in data:
        acc = (acc << 8) | byte
        acc_bits += 8
        while acc_bits >= bits:
            acc_bits -= bits
            values.append((acc >> acc_bits) & mask)
        acc &= (1 << acc_bits) - 1
    if acc_bits:
        values.append((acc << (bits - acc_bits)) & mask)
    return values


def unpack_values(values, bits, byte_len):
    result = bytearray()
    acc = 0
    acc_bits = 0
    for v in values:
        acc = (acc << bits) | v
        acc_bits += bits
        while acc_bits >= 8:
            acc_bits -= 8
            result.append((acc >> acc_bits) & 0xFF)
            if len(result) == byte_len:
                return bytes(result)
        acc &= (1 << acc_bits) - 1
    raise ValueError("隐写数据长度无效或图片已损坏")


def keystream(seed, domain, size):
    out = bytearray()
    counter = 0
    while len(out) < size:
        out += hashlib.sha256(seed + domain + counter.to_bytes(8, "big")).digest()
        counter += 1
    return bytes(out[:size])


def kdf_candidates():
    if Argon2id is not None:
        return ("argon2id", "pbkdf2")
    return ("pbkdf2",)


def derive_seed(password, salt, kdf_name, length):
    pw = password.encode("utf-8")
    if kdf_name == "argon2id":
        return Argon2id(
            salt=salt,
            length=length,
            iterations=ARGON2_ITERATIONS,
            lanes=ARGON2_LANES,
            memory_cost=ARGON2_MEMORY_KIB,
        ).derive(pw)
    return PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=length,
        salt=salt,
        iterations=PBKDF2_ITERATIONS,
    ).derive(pw)


def boot_seed(password, size, kdf_name):
    # salt 藏在头部里，而头部位置又依赖种子：用固定域盐派生引导种子，破解先后依赖
    domain = BOOT_DOMAIN + struct.pack(">II", *size)
    return derive_seed(password, domain, kdf_name, KEY_SIZE)


def position_stream(seed, pool_size, count):
    pool = list(range(pool_size))
    counter = 0
    buf = b""
    for i in range(count):
        while len(buf) < 8:
            buf += hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
            counter += 1
        value = int.from_bytes(buf[:8], "big")
        buf = buf[8:]
        j = i + value % (pool_size - i)
        pool[i], pool[j] = pool[j], pool[i]
        yield pool[i]


def compress_payload(data, codec):
    if codec == "auto":
        candidates = [(CODEC_IDS["none"], data)]
        candidates.extend(compress_payload(data, name) for name in ("gzip", "bzip2", "xz"))
        return min(candidates, key=lambda item: len(item[1]))
    if codec == "none":
        return CODEC_IDS[codec], data
    if codec == "gzip":
        return CODEC_IDS[codec], gzip.compress(data, compresslevel=9, mtime=0)
    if codec == "bzip2":
        return CODEC_IDS[codec], bz2.compress(data, compresslevel=9)
    if codec == "xz":
        return CODEC_IDS[codec], lzma.compress(data, format=lzma.FORMAT_XZ, preset=6)
    raise ValueError(f"不支持的压缩格式：{codec}")


def decompress_payload(data, codec_id):
    if codec_id not in ID_CODECS:
        raise ValueError("隐写数据格式无效或图片已损坏")
    codec = ID_CODECS[codec_id]
    if codec == "none":
        return data
    if codec == "gzip":
        return gzip.decompress(data)
    if codec == "bzip2":
        return bz2.decompress(data)
    return lzma.decompress(data, format=lzma.FORMAT_XZ)


def read_header(size, raw, password):
    if len(raw) < 32:
        raise ValueError("图片中没有有效隐写数据")
    for kdf_name in kdf_candidates():
        seed = boot_seed(password, size, kdf_name)
        positions = position_stream(seed, len(raw), len(raw))
        lsb = [raw[next(positions)] & 1 for _ in range(32)]
        masked_magic = unpack_values(lsb, 1, 4)
        magic = bytes(
            a ^ b for a, b in zip(masked_magic, keystream(seed, b"mask", 4))
        )
        if magic not in MAGIC_SET:
            continue
        header_size = HEADER_SIZE_V3 if magic in V3_MAGIC_SET else HEADER_SIZE_V2
        if len(raw) < header_size * 8:
            raise ValueError("隐写数据长度无效或图片已损坏")
        lsb = [raw[next(positions)] & 1 for _ in range((header_size - 4) * 8)]
        masked = masked_magic + unpack_values(lsb, 1, header_size - 4)
        header = bytes(
            a ^ b for a, b in zip(masked, keystream(seed, b"mask", header_size))
        )
        return header, positions
    raise ValueError("口令错误或图片中没有隐写数据")


def shard_capacity(size, bits):
    raw_size = size[0] * size[1] * 3
    return max(0, (raw_size - HEADER_BITS_V3) * bits // 8)


def shard_output_path(output_path, index, count):
    if count == 1:
        return output_path
    path = Path(output_path)
    suffix = path.suffix or ".png"
    return str(path.with_name(f"{path.stem}_{index + 1:03d}{suffix}"))


def embed(cover_paths, payload_path, output_path, password, bits=1, codec="none"):
    if bits not in (1, 2, 3, 4):
        raise ValueError("每个通道的嵌入位数必须是 1、2、3 或 4")
    payload = Path(payload_path).read_bytes()
    codec_id, stored_payload = compress_payload(payload, codec)
    if len(stored_payload) > 0xFFFFFFFF - GCM_OVERHEAD:
        raise ValueError("压缩后数据过大：密文总长度不能超过 4 GiB")

    kdf_name = kdf_candidates()[0]
    magic = MAGIC_ARGON2_V3 if kdf_name == "argon2id" else MAGIC_PBKDF2_V3
    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    enc_key = derive_seed(password, salt, kdf_name, KEY_SIZE)

    inner = bytes([codec_id]) + struct.pack(">I", len(stored_payload)) + stored_payload
    # 全局只加密一次，切分密文可避免各分片重复使用同一密钥和 nonce。
    ciphertext = AESGCM(enc_key).encrypt(nonce, inner, None)

    covers = []
    total_capacity = 0
    for cover_path in cover_paths:
        with Image.open(cover_path) as source:
            size = source.size
        capacity = shard_capacity(size, bits)
        if capacity <= 0:
            raise ValueError(f"载体图片太小，无法保存分片头部：{cover_path}")
        covers.append((cover_path, size, capacity))
        total_capacity += capacity
    if not covers:
        raise ValueError("至少需要一张载体图片")
    if len(ciphertext) > total_capacity:
        raise ValueError(
            f"所有图片总容量不足：密文为 {len(ciphertext)} 字节，"
            f"总容量为 {total_capacity} 字节，还差 {len(ciphertext) - total_capacity} 字节"
        )

    chunks = []
    offset = 0
    for cover_path, size, capacity in covers:
        if offset == len(ciphertext):
            break
        chunk_size = min(capacity, len(ciphertext) - offset)
        chunks.append((cover_path, size, offset, chunk_size))
        offset += chunk_size
    shard_count = len(chunks)
    if shard_count > MAX_SHARDS:
        raise ValueError(f"所需分片数量超过上限 {MAX_SHARDS}")

    output_paths = [
        shard_output_path(output_path, index, shard_count)
        for index in range(shard_count)
    ]
    cover_names = {os.path.abspath(path) for path, _, _ in covers}
    if any(os.path.abspath(path) in cover_names for path in output_paths):
        raise ValueError("输出文件不能覆盖任何输入载体图片")

    group_id = os.urandom(GROUP_ID_SIZE)
    for index, (cover_path, size, offset, chunk_size) in enumerate(chunks):
        with Image.open(cover_path) as source:
            image = source.convert("RGB")
        raw = bytearray(image.tobytes())
        header = SHARD_HEADER.pack(
            magic, salt, nonce, group_id,
            len(ciphertext), offset, chunk_size, bits, index, shard_count,
        )
        chunk = ciphertext[offset:offset + chunk_size]
        values = pack_values(chunk, bits)
        if HEADER_BITS_V3 + len(values) > len(raw):
            raise ValueError(f"分片容量计算不一致：{cover_path}")

        seed = boot_seed(password, size, kdf_name)
        positions = position_stream(seed, len(raw), len(raw))
        masked = bytes(
            a ^ b
            for a, b in zip(header, keystream(seed, b"mask", HEADER_SIZE_V3))
        )
        for bit in iter_bits(masked):
            pos = next(positions)
            raw[pos] = (raw[pos] & 0xFE) | bit
        keep = 0xFF & (0xFF << bits)
        for value in values:
            pos = next(positions)
            raw[pos] = (raw[pos] & keep) | value

        Image.frombytes("RGB", image.size, bytes(raw)).save(
            output_paths[index], format="PNG"
        )

    return len(payload), len(stored_payload), ID_CODECS[codec_id], output_paths


def decrypt_payload(ciphertext, salt, nonce, kdf_name, password):
    enc_key = derive_seed(password, salt, kdf_name, KEY_SIZE)
    try:
        inner = AESGCM(enc_key).decrypt(nonce, ciphertext, None)
    except InvalidTag:
        raise ValueError("口令错误或隐写数据已损坏") from None
    if len(inner) < 5:
        raise ValueError("隐写数据格式无效或图片已损坏")
    codec_id = inner[0]
    stored_size = struct.unpack(">I", inner[1:5])[0]
    if stored_size != len(inner) - 5:
        raise ValueError("隐写数据格式无效或图片已损坏")
    return decompress_payload(inner[5:], codec_id)


def extract_legacy(raw, header, positions, password):
    magic, salt, nonce, cipher_len, bits = LEGACY_HEADER.unpack(header)
    kdf_name = "argon2id" if magic == MAGIC_ARGON2 else "pbkdf2"
    if bits not in (1, 2, 3, 4) or cipher_len < GCM_OVERHEAD:
        raise ValueError("隐写数据格式无效或图片已损坏")
    needed = -(-cipher_len * 8 // bits)
    if HEADER_BITS_V2 + needed > len(raw):
        raise ValueError("隐写数据长度无效或图片已损坏")
    low_mask = (1 << bits) - 1
    values = [raw[next(positions)] & low_mask for _ in range(needed)]
    ciphertext = unpack_values(values, bits, cipher_len)
    return decrypt_payload(ciphertext, salt, nonce, kdf_name, password)


def extract(stego_paths, output_path, password):
    shards = []
    for stego_path in stego_paths:
        try:
            with Image.open(stego_path) as source:
                image = source.convert("RGB")
            raw = image.tobytes()
            header, positions = read_header(image.size, raw, password)
            magic = header[:4]
            if magic in V2_MAGIC_SET:
                if len(stego_paths) != 1:
                    raise ValueError("旧版 v2 单图文件必须单独提取")
                payload = extract_legacy(raw, header, positions, password)
                Path(output_path).write_bytes(payload)
                return

            (
                magic, salt, nonce, group_id, total_size,
                chunk_offset, chunk_size, bits, index, count,
            ) = SHARD_HEADER.unpack(header)
            kdf_name = "argon2id" if magic == MAGIC_ARGON2_V3 else "pbkdf2"
            if (
                bits not in (1, 2, 3, 4)
                or total_size < GCM_OVERHEAD
                or chunk_size == 0
                or count == 0
                or index >= count
                or chunk_offset >= total_size
                or chunk_size > total_size - chunk_offset
            ):
                raise ValueError("隐写分片头部无效或图片已损坏")

            needed = -(-chunk_size * 8 // bits)
            if HEADER_BITS_V3 + needed > len(raw):
                raise ValueError("隐写分片长度无效或图片已损坏")
            low_mask = (1 << bits) - 1
            values = [raw[next(positions)] & low_mask for _ in range(needed)]
            ciphertext = unpack_values(values, bits, chunk_size)
            shards.append({
                "magic": magic,
                "salt": salt,
                "nonce": nonce,
                "group_id": group_id,
                "total_size": total_size,
                "chunk_offset": chunk_offset,
                "chunk_size": chunk_size,
                "index": index,
                "count": count,
                "ciphertext": ciphertext,
                "kdf_name": kdf_name,
            })
        except ValueError as exc:
            raise ValueError(f"{stego_path}：{exc}") from None

    first = shards[0]
    shared_fields = ("magic", "salt", "nonce", "group_id", "total_size", "count")
    for shard in shards[1:]:
        if any(shard[field] != first[field] for field in shared_fields):
            raise ValueError("图片不属于同一隐写分组，或分组参数不一致")

    by_index = {}
    for shard in shards:
        index = shard["index"]
        if index in by_index:
            raise ValueError(f"分片序号重复：第 {index + 1} 片")
        by_index[index] = shard
    if len(shards) != first["count"]:
        missing = [
            index + 1 for index in range(first["count"])
            if index not in by_index
        ]
        shown = ", ".join(str(index) for index in missing[:20])
        if len(missing) > 20:
            shown += "..."
        raise ValueError(
            f"分片不完整：需要 {first['count']} 片，实际收到 {len(shards)} 片；"
            f"缺少序号：{shown}"
        )

    chunks = []
    expected_offset = 0
    for index in range(first["count"]):
        shard = by_index[index]
        if shard["chunk_offset"] != expected_offset:
            raise ValueError(f"第 {index + 1} 片的密文偏移不连续")
        chunks.append(shard["ciphertext"])
        expected_offset += shard["chunk_size"]
    if expected_offset != first["total_size"]:
        raise ValueError("分片总长度与头部声明不一致")

    ciphertext = b"".join(chunks)
    payload = decrypt_payload(
        ciphertext, first["salt"], first["nonce"], first["kdf_name"], password
    )
    Path(output_path).write_bytes(payload)


def main():
    parser = argparse.ArgumentParser(
        description="带口令保护的 PNG 多图分片隐写工具（v3，兼容 v2 提取）"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_embed = sub.add_parser("embed", help="将任意文件隐写到一张或多张 PNG")
    p_embed.add_argument("cover", nargs="+", help="一张或多张 PNG 载体图片")
    p_embed.add_argument("payload", help="ZIP、7Z、RAR、TAR、GZ、BZ2、XZ 等任意文件")
    p_embed.add_argument(
        "output", help="输出 PNG；多图时自动添加 _001、_002 等分片序号"
    )
    p_embed.add_argument(
        "--bits", type=int, choices=(1, 2, 3, 4), default=1,
        help="每通道嵌入位数：1（默认，最隐蔽）/ 2（×2）/ 3（×3）/ 4（×4）",
    )
    p_embed.add_argument(
        "--compress", choices=("none", "gzip", "bzip2", "xz", "auto"), default="none",
        help="隐写前压缩：none（默认）/ gzip / bzip2 / xz / auto（自动选择最小结果）",
    )

    p_extract = sub.add_parser("extract", help="从一张或多张隐写 PNG 还原原始文件")
    p_extract.add_argument("stego", nargs="+", help="全部隐写分片，输入顺序不限")
    p_extract.add_argument("output", help="输出文件，扩展名应与原文件一致")

    for p in (p_embed, p_extract):
        p.add_argument("-p", "--password", help="口令（省略则交互式输入，更安全）")

    args = parser.parse_args()
    password = args.password or getpass.getpass("请输入口令：")

    if args.command == "embed":
        original_size, stored_size, codec, output_paths = embed(
            args.cover, args.payload, args.output, password, args.bits, args.compress
        )
        if len(output_paths) == 1:
            print(f"已隐写：{output_paths[0]}")
        else:
            print(f"已隐写为 {len(output_paths)} 个分片：")
            for path in output_paths:
                print(f"  {path}")
        print(f"大小：{original_size} → {stored_size} 字节（内部压缩：{codec}）")
    else:
        extract(args.stego, args.output, password)
        print(f"已还原：{args.output}")


if __name__ == "__main__":
    main()
