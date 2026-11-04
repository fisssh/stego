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

SALT_SIZE = 16
NONCE_SIZE = 12
KEY_SIZE = 32
HEADER_SIZE = SALT_SIZE + NONCE_SIZE + 4 + 1
PBKDF2_ITERATIONS = 600_000
GCM_OVERHEAD = 1 + 4 + 16
CODEC_IDS = {"none": 0, "gzip": 1, "bzip2": 2, "xz": 3}
ID_CODECS = {value: key for key, value in CODEC_IDS.items()}


def iter_bits(data):
    for byte in data:
        for shift in range(7, -1, -1):
            yield (byte >> shift) & 1


def extract_bytes(raw, offset, bit_count):
    result = bytearray()
    for i in range(offset, offset + bit_count, 8):
        byte = 0
        for value in raw[i:i + 8]:
            byte = (byte << 1) | (value & 1)
        result.append(byte)
    return bytes(result)


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


def derive_keys(password, salt):
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=KEY_SIZE * 2,
        salt=salt,
        iterations=PBKDF2_ITERATIONS,
    )
    material = kdf.derive(password.encode("utf-8"))
    return material[:KEY_SIZE], material[KEY_SIZE:]


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


def embed(cover_path, payload_path, output_path, password, bits=1, codec="none"):
    image = Image.open(cover_path).convert("RGB")
    raw = bytearray(image.tobytes())
    payload = Path(payload_path).read_bytes()
    codec_id, stored_payload = compress_payload(payload, codec)

    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    enc_key, pos_seed = derive_keys(password, salt)

    inner = bytes([codec_id]) + struct.pack(">I", len(stored_payload)) + stored_payload
    ciphertext = AESGCM(enc_key).encrypt(nonce, inner, None)

    header = salt + nonce + struct.pack(">I", len(ciphertext)) + bytes([bits])
    header_bits = len(header) * 8
    values = pack_values(ciphertext, bits)

    if header_bits + len(values) > len(raw):
        capacity = (len(raw) - header_bits) * bits // 8 - GCM_OVERHEAD
        raise ValueError(
            f"图片容量不足：压缩后为 {len(stored_payload)} 字节，"
            f"当前 --bits {bits} 最多容纳 {capacity} 字节"
        )

    for i, bit in enumerate(iter_bits(header)):
        raw[i] = (raw[i] & 0xFE) | bit

    positions = position_stream(pos_seed, len(raw) - header_bits, len(values))
    mask = 0xFF & (0xFF << bits)
    for offset, v in zip(positions, values):
        pos = header_bits + offset
        raw[pos] = (raw[pos] & mask) | v

    Image.frombytes("RGB", image.size, bytes(raw)).save(output_path, format="PNG")
    return len(payload), len(stored_payload), ID_CODECS[codec_id]


def extract(stego_path, output_path, password):
    image = Image.open(stego_path).convert("RGB")
    raw = image.tobytes()

    if len(raw) < HEADER_SIZE * 8:
        raise ValueError("图片中没有有效隐写数据")

    header = extract_bytes(raw, 0, HEADER_SIZE * 8)
    salt = header[:SALT_SIZE]
    nonce = header[SALT_SIZE:SALT_SIZE + NONCE_SIZE]
    cipher_len = struct.unpack(">I", header[SALT_SIZE + NONCE_SIZE:SALT_SIZE + NONCE_SIZE + 4])[0]
    bits = header[-1]

    if bits not in (1, 2, 3, 4):
        raise ValueError("隐写数据格式无效或图片已损坏")

    header_bits = HEADER_SIZE * 8
    needed = -(-cipher_len * 8 // bits)
    if needed > len(raw) - header_bits:
        raise ValueError("隐写数据长度无效或图片已损坏")

    enc_key, pos_seed = derive_keys(password, salt)
    positions = position_stream(pos_seed, len(raw) - header_bits, needed)
    mask = (1 << bits) - 1
    values = [raw[header_bits + offset] & mask for offset in positions]
    ciphertext = unpack_values(values, bits, cipher_len)

    try:
        inner = AESGCM(enc_key).decrypt(nonce, ciphertext, None)
    except Exception:
        raise ValueError("口令错误或隐写数据已损坏") from None

    codec_id = inner[0]
    stored_size = struct.unpack(">I", inner[1:5])[0]
    stored_payload = inner[5:5 + stored_size]
    payload = decompress_payload(stored_payload, codec_id)
    Path(output_path).write_bytes(payload)


def main():
    parser = argparse.ArgumentParser(description="带口令保护的 PNG 压缩包隐写工具")
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
