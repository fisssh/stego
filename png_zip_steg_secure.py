import argparse
import getpass
import hashlib
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
HEADER_SIZE = SALT_SIZE + NONCE_SIZE + 4
PBKDF2_ITERATIONS = 600_000
GCM_OVERHEAD = 4 + 16


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


def embed(cover_path, zip_path, output_path, password):
    image = Image.open(cover_path).convert("RGB")
    raw = bytearray(image.tobytes())
    payload = Path(zip_path).read_bytes()

    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    enc_key, pos_seed = derive_keys(password, salt)

    inner = struct.pack(">I", len(payload)) + payload
    ciphertext = AESGCM(enc_key).encrypt(nonce, inner, None)

    header = salt + nonce + struct.pack(">I", len(ciphertext))
    header_bits = len(header) * 8
    if header_bits + len(ciphertext) * 8 > len(raw):
        capacity = (len(raw) - header_bits) // 8 - GCM_OVERHEAD
        raise ValueError(
            f"图片容量不足：ZIP 为 {len(payload)} 字节，最多容纳 {capacity} 字节"
        )

    for i, bit in enumerate(iter_bits(header)):
        raw[i] = (raw[i] & 0xFE) | bit

    positions = position_stream(pos_seed, len(raw) - header_bits, len(ciphertext) * 8)
    for offset, bit in zip(positions, iter_bits(ciphertext)):
        pos = header_bits + offset
        raw[pos] = (raw[pos] & 0xFE) | bit

    Image.frombytes("RGB", image.size, bytes(raw)).save(output_path, format="PNG")


def extract(stego_path, output_path, password):
    image = Image.open(stego_path).convert("RGB")
    raw = image.tobytes()

    if len(raw) < HEADER_SIZE * 8:
        raise ValueError("图片中没有有效隐写数据")

    header = extract_bytes(raw, 0, HEADER_SIZE * 8)
    salt = header[:SALT_SIZE]
    nonce = header[SALT_SIZE:SALT_SIZE + NONCE_SIZE]
    cipher_len = struct.unpack(">I", header[SALT_SIZE + NONCE_SIZE:])[0]

    header_bits = HEADER_SIZE * 8
    if cipher_len * 8 > len(raw) - header_bits:
        raise ValueError("隐写数据长度无效或图片已损坏")

    enc_key, pos_seed = derive_keys(password, salt)
    positions = position_stream(pos_seed, len(raw) - header_bits, cipher_len * 8)

    ciphertext = bytearray()
    byte = 0
    for i, offset in enumerate(positions):
        byte = (byte << 1) | (raw[header_bits + offset] & 1)
        if i % 8 == 7:
            ciphertext.append(byte)
            byte = 0

    try:
        inner = AESGCM(enc_key).decrypt(nonce, bytes(ciphertext), None)
    except Exception:
        raise ValueError("口令错误或隐写数据已损坏") from None

    payload_size = struct.unpack(">I", inner[:4])[0]
    Path(output_path).write_bytes(inner[4:4 + payload_size])


def main():
    parser = argparse.ArgumentParser(description="带口令保护的 PNG-ZIP 隐写工具")
    sub = parser.add_subparsers(dest="command", required=True)

    p_embed = sub.add_parser("embed", help="将 ZIP 隐写入 PNG")
    p_embed.add_argument("cover")
    p_embed.add_argument("zip")
    p_embed.add_argument("output")

    p_extract = sub.add_parser("extract", help="从 PNG 还原 ZIP")
    p_extract.add_argument("stego")
    p_extract.add_argument("output")

    for p in (p_embed, p_extract):
        p.add_argument("-p", "--password", help="口令（省略则交互式输入，更安全）")

    args = parser.parse_args()
    password = args.password or getpass.getpass("请输入口令：")

    if args.command == "embed":
        embed(args.cover, args.zip, args.output, password)
        print(f"已隐写：{args.output}")
    else:
        extract(args.stego, args.output, password)
        print(f"已还原：{args.output}")


if __name__ == "__main__":
    main()
