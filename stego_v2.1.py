import argparse
import bz2
import getpass
import gzip
import hashlib
import lzma
import os
import struct
from pathlib import Path

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
MAGIC_ARGON2 = b"SGA2"
MAGIC_PBKDF2 = b"SGP2"
MAGIC_SET = (MAGIC_ARGON2, MAGIC_PBKDF2)
HEADER_SIZE = 4 + SALT_SIZE + NONCE_SIZE + 4 + 1
HEADER_BITS = HEADER_SIZE * 8
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
    acc = 0
    acc_bits = 0
    mask = (1 << bits) - 1
    for byte in data:
        acc = (acc << 8) | byte
        acc_bits += 8
        while acc_bits >= bits:
            acc_bits -= bits
            yield (acc >> acc_bits) & mask
        acc &= (1 << acc_bits) - 1
    if acc_bits:
        yield (acc << (bits - acc_bits)) & mask


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
    swaps = {}
    counter = 0
    buf = b""
    for i in range(count):
        while len(buf) < 8:
            buf += hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
            counter += 1
        value = int.from_bytes(buf[:8], "big")
        buf = buf[8:]
        j = i + value % (pool_size - i)

        # swaps 仅保存尚未输出且被交换的位置，缺省下标映射到自身
        value_i = swaps.pop(i, i)
        if i == j:
            yield value_i
            continue
        selected = swaps.get(j, j)
        swaps[j] = value_i
        yield selected


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
    for kdf_name in kdf_candidates():
        seed = boot_seed(password, size, kdf_name)
        positions = position_stream(seed, len(raw), len(raw))
        lsb = [raw[next(positions)] & 1 for _ in range(HEADER_BITS)]
        masked = unpack_values(lsb, 1, HEADER_SIZE)
        header = bytes(a ^ b for a, b in zip(masked, keystream(seed, b"mask", HEADER_SIZE)))
        if header[:4] in MAGIC_SET:
            return header, positions
    raise ValueError("口令错误或图片中没有隐写数据")


def embed(cover_path, payload_path, output_path, password, bits=1, codec="none"):
    image = Image.open(cover_path).convert("RGB")
    raw = bytearray(image.tobytes())
    payload = Path(payload_path).read_bytes()
    codec_id, stored_payload = compress_payload(payload, codec)

    kdf_name = kdf_candidates()[0]
    magic = MAGIC_ARGON2 if kdf_name == "argon2id" else MAGIC_PBKDF2
    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    enc_key = derive_seed(password, salt, kdf_name, KEY_SIZE)

    inner = bytes([codec_id]) + struct.pack(">I", len(stored_payload)) + stored_payload
    ciphertext = AESGCM(enc_key).encrypt(nonce, inner, None)

    # 头部明文含低熵字段（magic/长度/bits），先 XOR 掩码再写入，使全部嵌入位均为均匀随机
    header = magic + salt + nonce + struct.pack(">I", len(ciphertext)) + bytes([bits])
    needed = -(-len(ciphertext) * 8 // bits)

    if HEADER_BITS + needed > len(raw):
        capacity = (len(raw) - HEADER_BITS) * bits // 8 - GCM_OVERHEAD
        raise ValueError(
            f"图片容量不足：压缩后为 {len(stored_payload)} 字节，"
            f"当前 --bits {bits} 最多容纳 {capacity} 字节"
        )

    # 头部与载荷共用同一条惰性位置流：先消费 296 个位置写头部 LSB，再续用写载荷
    seed = boot_seed(password, image.size, kdf_name)
    positions = position_stream(seed, len(raw), len(raw))
    masked = bytes(a ^ b for a, b in zip(header, keystream(seed, b"mask", HEADER_SIZE)))

    for bit in iter_bits(masked):
        pos = next(positions)
        raw[pos] = (raw[pos] & 0xFE) | bit
    keep = 0xFF & (0xFF << bits)
    for v in pack_values(ciphertext, bits):
        pos = next(positions)
        raw[pos] = (raw[pos] & keep) | v

    Image.frombytes("RGB", image.size, bytes(raw)).save(output_path, format="PNG")
    return len(payload), len(stored_payload), ID_CODECS[codec_id]


def extract(stego_path, output_path, password):
    image = Image.open(stego_path).convert("RGB")
    raw = image.tobytes()

    if len(raw) < HEADER_BITS:
        raise ValueError("图片中没有有效隐写数据")

    header, positions = read_header(image.size, raw, password)
    magic = header[:4]
    kdf_name = "argon2id" if magic == MAGIC_ARGON2 else "pbkdf2"
    salt = header[4:4 + SALT_SIZE]
    nonce = header[4 + SALT_SIZE:4 + SALT_SIZE + NONCE_SIZE]
    cipher_len = struct.unpack(">I", header[4 + SALT_SIZE + NONCE_SIZE:HEADER_SIZE - 1])[0]
    bits = header[-1]

    if bits not in (1, 2, 3, 4) or cipher_len == 0:
        raise ValueError("隐写数据格式无效或图片已损坏")

    needed = -(-cipher_len * 8 // bits)
    if HEADER_BITS + needed > len(raw):
        raise ValueError("隐写数据长度无效或图片已损坏")

    low_mask = (1 << bits) - 1
    values = (raw[next(positions)] & low_mask for _ in range(needed))
    ciphertext = unpack_values(values, bits, cipher_len)

    enc_key = derive_seed(password, salt, kdf_name, KEY_SIZE)
    try:
        inner = AESGCM(enc_key).decrypt(nonce, ciphertext, None)
    except Exception:
        raise ValueError("口令错误或隐写数据已损坏") from None

    codec_id = inner[0]
    stored_size = struct.unpack(">I", inner[1:5])[0]
    if stored_size > len(inner) - 5:
        raise ValueError("隐写数据格式无效或图片已损坏")
    payload = decompress_payload(inner[5:5 + stored_size], codec_id)
    Path(output_path).write_bytes(payload)


def main():
    parser = argparse.ArgumentParser(description="带口令保护的 PNG 压缩包隐写工具（散射头部 v2）")
    sub = parser.add_subparsers(dest="command", required=True)

    p_embed = sub.add_parser("embed", help="将压缩包隐写入 PNG")
    p_embed.add_argument("cover", help="PNG 载体图片")
    p_embed.add_argument("payload", help="ZIP、7Z、RAR、TAR、GZ、BZ2、XZ 等任意文件")
    p_embed.add_argument("output", help="输出的隐写 PNG")
    p_embed.add_argument(
        "--bits", type=int, choices=(1, 2, 3, 4), default=1,
        help="每通道嵌入位数：1（默认，最隐蔽）/ 2（×2）/ 3（×3）/ 4（×4）",
    )
    p_embed.add_argument(
        "--compress", choices=("none", "gzip", "bzip2", "xz", "auto"), default="none",
        help="隐写前压缩：none（默认）/ gzip / bzip2 / xz / auto（自动选择最小结果）",
    )

    p_extract = sub.add_parser("extract", help="从 PNG 还原原始压缩包")
    p_extract.add_argument("stego", help="隐写 PNG")
    p_extract.add_argument("output", help="输出文件，扩展名应与原文件一致")

    for p in (p_embed, p_extract):
        p.add_argument("-p", "--password", help="口令（省略则交互式输入，更安全）")

    args = parser.parse_args()
    password = args.password or getpass.getpass("请输入口令：")

    if args.command == "embed":
        original_size, stored_size, codec = embed(
            args.cover, args.payload, args.output, password, args.bits, args.compress
        )
        print(f"已隐写：{args.output}")
        print(f"大小：{original_size} → {stored_size} 字节（内部压缩：{codec}）")
    else:
        extract(args.stego, args.output, password)
        print(f"已还原：{args.output}")


if __name__ == "__main__":
    main()
