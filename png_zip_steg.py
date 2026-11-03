import struct
import sys
from pathlib import Path

from PIL import Image

MAGIC = b"ZSTG"
HEADER_SIZE = 8


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


def embed(cover_path, zip_path, output_path):
    image = Image.open(cover_path).convert("RGB")
    raw = bytearray(image.tobytes())
    payload = Path(zip_path).read_bytes()
    blob = MAGIC + struct.pack(">I", len(payload)) + payload

    if len(blob) * 8 > len(raw):
        capacity = len(raw) // 8 - HEADER_SIZE
        raise ValueError(
            f"图片容量不足：ZIP 为 {len(payload)} 字节，"
            f"最多容纳 {capacity} 字节"
        )

    for i, bit in enumerate(iter_bits(blob)):
        raw[i] = (raw[i] & 0xFE) | bit

    result = Image.frombytes("RGB", image.size, bytes(raw))
    result.save(output_path, format="PNG")


def extract(stego_path, output_path):
    image = Image.open(stego_path).convert("RGB")
    raw = image.tobytes()

    if len(raw) < HEADER_SIZE * 8:
        raise ValueError("图片中没有有效隐写数据")

    header = extract_bytes(raw, 0, HEADER_SIZE * 8)

    if header[:4] != MAGIC:
        raise ValueError("未找到隐写数据标记")

    payload_size = struct.unpack(">I", header[4:])[0]

    if payload_size > (len(raw) - HEADER_SIZE * 8) // 8:
        raise ValueError("隐写数据长度无效或图片已损坏")

    payload = extract_bytes(raw, HEADER_SIZE * 8, payload_size * 8)
    Path(output_path).write_bytes(payload)


if __name__ == "__main__":
    command = sys.argv[1] if len(sys.argv) > 1 else ""
    valid_args = (
        (command == "embed" and len(sys.argv) == 5)
        or (command == "extract" and len(sys.argv) == 4)
    )
    if not valid_args:
        print(f"用法：")
        print(f"  python {sys.argv[0]} embed cover.png secret.zip stego.png")
        print(f"  python {sys.argv[0]} extract stego.png recovered.zip")
        sys.exit(1)

    if command == "embed":
        embed(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        extract(sys.argv[2], sys.argv[3])
