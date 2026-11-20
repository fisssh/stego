#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
基于全谱系 12 档动态负载率自适应广义 n-EMD / 正交多进制 / 钻石编码 (DE-13) +
X25519 Elligator 2 ECIES / AES-256-GCM 的高隐蔽性图像隐写与配对脚本生成工具 (v3.3.1 全谱系升级版)

核心特性：
  1. 全谱系 12 档动态负载率自适应调制引擎（11 档 --profile auto 自动择优 + 1 档显式应急，100% 兼容 v3.2）：
     - [幽灵微隐写档] emd64 (模129, 1.55%) / emd32 (模65, 3.08%) / emd16 (模33, 6.06%) —— 极小文本与密钥
     - [隐蔽文档档  ] emd8  (模17, 11.76%) / emd6  (模13, 15.38%) / emd4 (模9, 22.22%)  —— 中小文档与压缩包
     - [高容均衡档  ] emd3  (模7,  28.57%) / emd2  (模5,  40.00%) / base3 (模3, ±1满邻域 1.585 bpc)
     - [极限载荷档  ] de13  (钻石模13, 1.851 bpc) / base5 (模5, ±2正交晶格 2.318 bpc)
     - [显式应急档  ] base7 (模7, ±3正交晶格 2.807 bpc，仅手动指定，防止 auto 静默降低画质)
  2. 原生图像元数据与色彩配置无痕透传引擎（PNG 二进制块级无损注入）：
     - 自动提取并原样克隆载体图像的 ICC Profile 色彩配置、EXIF 拍摄信息、DPI 物理尺寸及 PNG 标准辅助块
       (gAMA / cHRM / iCCP / sRGB / pHYs / tIME / eXIf / tEXt / zTXt / iTXt / mDCV / cLLI 等)，消除偏色与“裸 PNG 元数据丢失”特征
     - 支持 16-bit 灰度图像安全降采样防截断保护，内置像素级 PSNR (dB) 量化评估（支持可选 NumPy 加速）
  3. 盲提取零特征头部自举协议（EMD3 v3）：
     - 引导头与加密元数据头固定采用高隐蔽性 emd8 (模 17, 11.76% 修改率) 嵌入
     - 载荷调制档位 ID (0~15) 与压缩算法 ID 封装在 AES-256-GCM 认证加密元数据内部，提取端全自动盲识别切换
  4. 双密码学引擎：
     - 非对称公钥模式：X25519 + 全群 Elligator 2 隐匿（消除二次剩余与 Cofactor-8 子群偏置）+ HKDF-SHA256 + 双层 AES-256-GCM
     - 对称口令模式  ：随机引导盐 + PBKDF2-HMAC-SHA256 + HKDF + 双层 AES-256-GCM（一图一密一轨迹）
  5. 重装加固版配对脚本生成器（pairgen）：
     - 密钥 4 路 256-bit 异或代数分片重构（零 Hex 密钥特征）+ AST 控制流平坦化与不透明谓词 + Marshal 字节码 PBKDF2 加密壳
"""

# === [PAIR_SHARED_CORE_START] ===
import argparse
import bz2
import gzip
import hashlib
import io
import lzma
import math
import os
import struct
import sys
import zlib
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence, Set, Tuple

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import x25519
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from PIL import Image, PngImagePlugin

try:
    import numpy as np  # 可选加速：存在时显著提升大图像 PSNR 计算性能
except ImportError:
    np = None  # type: ignore[assignment]

# ==================== 协议常量与全谱系自适应调制档位参数 ====================

MAGIC = b"EMD3"
FORMAT_VERSION = 3

SALT_SIZE = 16                  # 随机盐长度（字节）
NONCE_SIZE = 12                 # AES-GCM Nonce 长度（字节）
KEY_SIZE = 32                   # 对称密钥 / 种子长度（字节）
GCM_TAG_SIZE = 16               # AES-GCM 认证标签长度（字节）
EPHEMERAL_PUBLIC_SIZE = 32      # Elligator 2 临时公钥代表元长度（字节）

ASYM_BOOT_SIZE = EPHEMERAL_PUBLIC_SIZE + SALT_SIZE  # 非对称引导头：48 字节
SYM_BOOT_SIZE = SALT_SIZE                           # 对称引导头：16 字节
META_PLAIN_SIZE = 4 + 1 + 1 + 4                     # MAGIC(4) + VER(1) + PROF_CODEC(1) + CIPHER_LEN(4) = 10 字节
META_CIPHER_SIZE = META_PLAIN_SIZE + GCM_TAG_SIZE   # 加密元数据头：26 字节

PUBLIC_BOOT_DOMAIN = b"EMD-Stego-v3-Public-Bootstrap"
SYM_BOOT_DOMAIN = b"EMD-Stego-v3-Password-Bootstrap"
ECIES_KDF_DOMAIN = b"EMD-Stego-v3-X25519-Elligator2-HKDF"
SYM_KDF_DOMAIN = b"EMD-Stego-v3-Symmetric-HKDF"
MASK_DOMAIN = b"EMD-Stego-v3-Bootstrap-Mask"
STREAM_DOMAIN = b"EMD-Stego-v3-Position-Stream"

CODEC_IDS = {"none": 0, "gzip": 1, "bzip2": 2, "xz": 3}
ID_CODECS = {val: name for name, val in CODEC_IDS.items()}

# 允许从原 PNG 无损透传至隐写 PNG 的安全辅助块白名单
# （排除 IHDR/PLTE/IDAT/IEND/tRNS/bKGD/hIST 等与像素结构或调色板强绑定的块，避免重编码后校验冲突）
_SAFE_PNG_ANCILLARY_CHUNKS: Set[bytes] = {
    b"cHRM",  # 基色色度坐标
    b"gAMA",  # Gamma 曲线
    b"iCCP",  # 嵌入式 ICC 色彩配置
    b"sRGB",  # 标准 sRGB 色彩空间标记
    b"cICP",  # 编码独立色彩点 (HDR/广色域标记)
    b"mDCV",  # 主显示色彩体积
    b"cLLI",  # 内容光级信息
    b"pHYs",  # 物理像素尺寸 / DPI
    b"sPLT",  # 建议调色板
    b"tIME",  # 图像最后修改时间块
    b"eXIf",  # 原生 EXIF 元数据块
    b"tEXt",  # 标准文本注释块
    b"zTXt",  # 压缩文本注释块
    b"iTXt",  # 国际化 UTF-8/XMP 文本块
    b"caBX",  # C2PA / 相机内容凭证块
}


class ModulationProfile:
    """广义 n-EMD / 单通道正交多进制 / 钻石编码调制档位定义及预计算分块基数换算表"""

    def __init__(
        self,
        prof_id: int,
        key: str,
        title: str,
        group_size: int,
        radix: int,
        block_bytes: int,
        expected_mod_rate: float,
        max_delta: int,
        kind: str,
        auto_eligible: bool = True,
    ) -> None:
        self.prof_id = prof_id
        self.key = key
        self.title = title
        self.group_size = group_size
        self.radix = radix
        self.block_bytes = block_bytes
        self.expected_mod_rate = expected_mod_rate  # 理论通道修改率百分比
        self.max_delta = max_delta                  # 正常区单通道最大振幅 (L∞)
        self.kind = kind                            # "gemd" | "base_m" | "diamond13"
        self.auto_eligible = auto_eligible          # 是否允许 --profile auto 自动选用

        # 预计算 0..block_bytes 字节各自所需的最小 M 进制位数 d（满足 radix^d >= 256^b）
        self.digits_for_bytes: List[int] = [0]
        for b_len in range(1, block_bytes + 1):
            limit = 1 << (8 * b_len)
            digits, power = 0, 1
            while power < limit:
                power *= radix
                digits += 1
            self.digits_for_bytes.append(digits)

        self.block_digits = self.digits_for_bytes[block_bytes]
        self.bpc = (block_bytes * 8.0) / (self.block_digits * group_size)


# 全谱系 12 档自适应隐写配置（按容量递增 / 失真 MSE 递增严格排序；严格保留 v3.2 旧版 ID 0~3 实现 100% 向后兼容）：
#   ID 4 : emd64 -> n=64, M=129, 256^7  < 129^8   (效率 99.84%, 0.109 bpc, 修改率 ~1.55%,  ±1)
#   ID 5 : emd32 -> n=32, M=65,  256^3  < 65^4    (效率 99.63%, 0.188 bpc, 修改率 ~3.08%,  ±1)
#   ID 6 : emd16 -> n=16, M=33,  256^17 < 33^27   (效率 99.85%, 0.315 bpc, 修改率 ~6.06%,  ±1)
#   ID 0 : emd8  -> n=8,  M=17,  256^48 < 17^94   (效率 99.84%, 0.509 bpc, 修改率 ~11.76%, ±1) [兼容 v3.2]
#   ID 7 : emd6  -> n=6,  M=13,  256^31 < 13^67   (效率 99.99%, 0.617 bpc, 修改率 ~15.38%, ±1)
#   ID 1 : emd4  -> n=4,  M=9,   256^32 < 9^81    (效率 99.70%, 0.790 bpc, 修改率 ~22.22%, ±1) [兼容 v3.2]
#   ID 8 : emd3  -> n=3,  M=7,   256^20 < 7^57    (效率 99.99%, 0.936 bpc, 修改率 ~28.57%, ±1)
#   ID 2 : emd2  -> n=2,  M=5,   256^37 < 5^128   (效率 99.60%, 1.156 bpc, 修改率 ~40.00%, ±1) [兼容 v3.2]
#   ID 9 : base3 -> n=1,  M=3,   256^21 < 3^106   (效率 99.99%, 1.585 bpc, 修改率 ~66.67%, ±1 满邻域极限)
#   ID 3 : de13  -> n=2,  M=13,  256^31 < 13^67   (效率 99.99%, 1.851 bpc, 修改率 ~61.54%, ±2) [兼容 v3.2]
#   ID 10: base5 -> n=1,  M=5,   256^31 < 5^107   (效率 99.82%, 2.318 bpc, 修改率 ~80.00%, ±2 正交晶格)
#   ID 11: base7 -> n=1,  M=7,   256^20 < 7^57    (效率 99.99%, 2.807 bpc, 修改率 ~85.71%, ±3 显式应急档)
PROFILES_ORDERED: List[ModulationProfile] = [
    ModulationProfile(
        prof_id=4,
        key="emd64",
        title="64-通道广义 EMD (模 129 · 幽灵微隐写档)",
        group_size=64,
        radix=129,
        block_bytes=7,
        expected_mod_rate=(128.0 / 129.0) / 64.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=5,
        key="emd32",
        title="32-通道广义 EMD (模 65 · 超微文本隐写档)",
        group_size=32,
        radix=65,
        block_bytes=3,
        expected_mod_rate=(64.0 / 65.0) / 32.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=6,
        key="emd16",
        title="16-通道广义 EMD (模 33 · 微型文档隐写档)",
        group_size=16,
        radix=33,
        block_bytes=17,
        expected_mod_rate=(32.0 / 33.0) / 16.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=0,
        key="emd8",
        title="8-通道广义 EMD (模 17 · 常规文档隐蔽档)",
        group_size=8,
        radix=17,
        block_bytes=48,
        expected_mod_rate=(16.0 / 17.0) / 8.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=7,
        key="emd6",
        title="6-通道广义 EMD (模 13 · 中小文件过渡档)",
        group_size=6,
        radix=13,
        block_bytes=31,
        expected_mod_rate=(12.0 / 13.0) / 6.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=1,
        key="emd4",
        title="4-通道广义 EMD (模 9 · 中等文件隐蔽档)",
        group_size=4,
        radix=9,
        block_bytes=32,
        expected_mod_rate=(8.0 / 9.0) / 4.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=8,
        key="emd3",
        title="3-通道广义 EMD (模 7 · 中大文件过渡档)",
        group_size=3,
        radix=7,
        block_bytes=20,
        expected_mod_rate=(6.0 / 7.0) / 3.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=2,
        key="emd2",
        title="2-通道经典 EMD (模 5 · 大文件均衡档)",
        group_size=2,
        radix=5,
        block_bytes=37,
        expected_mod_rate=(4.0 / 5.0) / 2.0 * 100.0,
        max_delta=1,
        kind="gemd",
    ),
    ModulationProfile(
        prof_id=9,
        key="base3",
        title="单通道 3 进制正交晶格 (±1 振幅极限档)",
        group_size=1,
        radix=3,
        block_bytes=21,
        expected_mod_rate=(2.0 / 3.0) * 100.0,
        max_delta=1,
        kind="base_m",
    ),
    ModulationProfile(
        prof_id=3,
        key="de13",
        title="双像素钻石编码 DE (模 13 · 高容量档)",
        group_size=2,
        radix=13,
        block_bytes=31,
        # 模 13 菱形晶格 13 个余数类中：1个改0通道、8个改1通道、4个改2通道 -> 总修改 16 通道 / 26 通道 = 61.54%
        expected_mod_rate=(16.0 / 13.0) / 2.0 * 100.0,
        max_delta=2,
        kind="diamond13",
    ),
    ModulationProfile(
        prof_id=10,
        key="base5",
        title="单通道 5 进制正交晶格 (±2 极限高容档)",
        group_size=1,
        radix=5,
        block_bytes=31,
        expected_mod_rate=(4.0 / 5.0) * 100.0,
        max_delta=2,
        kind="base_m",
    ),
    ModulationProfile(
        prof_id=11,
        key="base7",
        title="单通道 7 进制正交晶格 (±3 显式应急档)",
        group_size=1,
        radix=7,
        block_bytes=20,
        expected_mod_rate=(6.0 / 7.0) * 100.0,
        max_delta=3,
        kind="base_m",
        auto_eligible=False,
    ),
]

AUTO_PROFILES: List[ModulationProfile] = [p for p in PROFILES_ORDERED if p.auto_eligible]
PROFILE_BY_KEY: Dict[str, ModulationProfile] = {p.key: p for p in PROFILES_ORDERED}
PROFILE_BY_ID: Dict[int, ModulationProfile] = {p.prof_id: p for p in PROFILES_ORDERED}
PROFILE_CHOICES: Tuple[str, ...] = ("auto",) + tuple(p.key for p in PROFILES_ORDERED)

# 引导头与元数据头固定使用 emd8（模 17，修改率 11.76%），兼顾极高隐蔽性与旧版盲提取协议 100% 兼容
HEADER_PROFILE = PROFILE_BY_KEY["emd8"]

# 预计算双像素边界回退偏移表：
# 1) 双像素 EMD (n=2) 边界搜索表：优先保证 L∞ 最小，其次 L1 最小
_PAIR_EMD_OFFSETS: List[Tuple[int, int]] = sorted(
    [(d1, d2) for d1 in range(-2, 3) for d2 in range(-2, 3) if (d1, d2) != (0, 0)],
    key=lambda item: (max(abs(item[0]), abs(item[1])), abs(item[0]) + abs(item[1])),
)

# 2) 模 13 钻石编码 (Diamond Encoding, k=2, f = (p1 + 5*p2) % 13) 核心映射表与边界回退表
_DE13_CANDIDATES: List[Tuple[int, int]] = sorted(
    [(d1, d2) for d1 in range(-2, 3) for d2 in range(-2, 3)],
    key=lambda item: (
        abs(item[0]) + abs(item[1]),
        item[0] * item[0] + item[1] * item[1],
        max(abs(item[0]), abs(item[1])),
    ),
)
_DE13_PRIMARY_DELTAS: Dict[int, Tuple[int, int]] = {}
for _d1, _d2 in _DE13_CANDIDATES:
    _rem = (_d1 + 5 * _d2) % 13
    if _rem not in _DE13_PRIMARY_DELTAS:
        _DE13_PRIMARY_DELTAS[_rem] = (_d1, _d2)

if len(_DE13_PRIMARY_DELTAS) != 13:
    raise RuntimeError("钻石编码 (模 13) 菱形晶格自检失败：未能覆盖全部 13 个余数类")

_DE13_BOUNDARY_OFFSETS: List[Tuple[int, int]] = sorted(
    [(d1, d2) for d1 in range(-4, 5) for d2 in range(-4, 5) if (d1, d2) != (0, 0)],
    key=lambda item: (
        abs(item[0]) + abs(item[1]),
        max(abs(item[0]), abs(item[1])),
        item[0] * item[0] + item[1] * item[1],
    ),
)


# ==================== Curve25519 全群 Elligator 2 公钥隐匿层 ====================

_P25519 = (1 << 255) - 19
_P25519_HALF = (_P25519 - 1) // 2  # 2^254 - 10
_A25519 = 486662
_SQRT_M1 = pow(2, (_P25519 - 1) // 4, _P25519)
_ED25519_D = (-121665 * pow(121666, _P25519 - 2, _P25519)) % _P25519


def _sqrt_mod_p(a: int) -> Optional[int]:
    """计算 GF(2^255 - 19) 上的非负平方根 r ∈ [0, (p-1)/2]；若非二次剩余则返回 None"""
    a %= _P25519
    r = pow(a, (_P25519 + 3) // 8, _P25519)
    if (r * r) % _P25519 != a:
        r = (r * _SQRT_M1) % _P25519
        if (r * r) % _P25519 != a:
            return None
    if r > _P25519_HALF:
        r = _P25519 - r
    return r


def _ed25519_add(pt1: Tuple[int, int], pt2: Tuple[int, int]) -> Tuple[int, int]:
    """Edwards25519 (-x^2 + y^2 = 1 + d*x^2*y^2) 完备群加法（在整条曲线上无任何奇异点）"""
    x1, y1 = pt1
    x2, y2 = pt2
    x1x2 = (x1 * x2) % _P25519
    y1y2 = (y1 * y2) % _P25519
    dxxyy = (_ED25519_D * x1x2 * y1y2) % _P25519
    x3 = ((x1 * y2 + y1 * x2) * pow(1 + dxxyy, _P25519 - 2, _P25519)) % _P25519
    y3 = ((y1y2 + x1x2) * pow(1 - dxxyy, _P25519 - 2, _P25519)) % _P25519
    return x3, y3


def _build_ed25519_low_order_points() -> List[Tuple[int, int]]:
    """通过代数方程 d*y^4 + 2*y^2 - 1 = 0 构造并校验 Edwards25519 全部 8 个低阶挠点 E[8]"""
    s = _sqrt_mod_p(_ED25519_D + 1)
    if s is None:
        raise RuntimeError("Edwards25519 参数自检失败：d + 1 非二次剩余")
    inv_d = pow(_ED25519_D, _P25519 - 2, _P25519)
    yh = _sqrt_mod_p((-1 + s) * inv_d)
    if yh is None:
        yh = _sqrt_mod_p((-1 - s) * inv_d)
    if yh is None:
        raise RuntimeError("Edwards25519 8 阶挠点求解失败")
    xh = (_SQRT_M1 * yh) % _P25519
    gen = (xh, yh)

    pts: List[Tuple[int, int]] = [(0, 1)]
    cur = (0, 1)
    for _ in range(1, 8):
        cur = _ed25519_add(cur, gen)
        pts.append(cur)

    if pts[4] != (0, _P25519 - 1) or _ed25519_add(pts[7], gen) != (0, 1):
        raise RuntimeError("Edwards25519 8 阶挠点群校验未通过")
    return pts


_ED25519_LOW_ORDER_POINTS: List[Tuple[int, int]] = _build_ed25519_low_order_points()


def _elligator2_r_to_u(r: int) -> int:
    """Elligator 2 正向映射（Direct Map, Z = 2）：将任意域元素 r 确定性映射为合法 Curve25519 坐标 u"""
    r %= _P25519
    denom = (1 + 2 * r * r) % _P25519
    w = (-_A25519 * pow(denom, _P25519 - 2, _P25519)) % _P25519
    w_rhs = (w * (w * w + _A25519 * w + 1)) % _P25519
    is_sq = pow(w_rhs, _P25519_HALF, _P25519) == 1
    return w if is_sq else (-w - _A25519) % _P25519


def _elligator2_encode_u(u: int) -> Optional[bytes]:
    """Elligator 2 逆向映射：若坐标 u 存在原像（~50% 概率），返回最高 2 比特随机化填充后的 32 字节代表元"""
    u %= _P25519
    toss = os.urandom(1)[0]
    if u == 0:
        if toss & 0x01:
            return None
        r = 0
    else:
        u_plus_a = (u + _A25519) % _P25519
        if u_plus_a == 0:
            return None
        if toss & 0x01:
            r_sq = (-u_plus_a * pow(2 * u, _P25519 - 2, _P25519)) % _P25519
        else:
            r_sq = (-u * pow(2 * u_plus_a, _P25519 - 2, _P25519)) % _P25519
        r_opt = _sqrt_mod_p(r_sq)
        if r_opt is None:
            return None
        r = r_opt

    rep = bytearray(r.to_bytes(32, "little"))
    rep[31] = (rep[31] & 0x3F) | (toss & 0xC0)
    return bytes(rep)


def elligator2_decode(rep_bytes: bytes) -> bytes:
    """将任意 32 字节代表元（或随机噪点）无条件还原为合法的 32 字节 X25519 公钥坐标 u"""
    if len(rep_bytes) != EPHEMERAL_PUBLIC_SIZE:
        raise ValueError("Elligator 2 代表元长度必须为 32 字节。")
    r = int.from_bytes(rep_bytes, "little") & ((1 << 254) - 1)
    u = _elligator2_r_to_u(r)
    return u.to_bytes(32, "little")


def serialize_x25519_public(public_key: x25519.X25519PublicKey) -> bytes:
    """将 X25519 公钥序列化为 32 字节原始格式"""
    return public_key.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )


def generate_elligator2_ephemeral() -> Tuple[x25519.X25519PrivateKey, bytes, bytes]:
    """生成支持全群 Elligator 2 均匀伪装的 X25519 临时密钥对"""
    while True:
        ephemeral_private = x25519.X25519PrivateKey.generate()
        u_base_bytes = serialize_x25519_public(ephemeral_private.public_key())
        u_base = int.from_bytes(u_base_bytes, "little") % _P25519
        if u_base == 0 or (u_base + 1) % _P25519 == 0:
            continue

        y_ed = ((u_base - 1) * pow(u_base + 1, _P25519 - 2, _P25519)) % _P25519
        x_sq_num = (y_ed * y_ed - 1) % _P25519
        x_sq_den = (_ED25519_D * y_ed * y_ed + 1) % _P25519
        x_ed = _sqrt_mod_p(x_sq_num * pow(x_sq_den, _P25519 - 2, _P25519))
        if x_ed is None:
            continue

        rand_byte = os.urandom(1)[0]
        if rand_byte & 0x08:
            x_ed = (-x_ed) % _P25519

        low_pt = _ED25519_LOW_ORDER_POINTS[rand_byte & 0x07]
        _, y_full = _ed25519_add((x_ed, y_ed), low_pt)
        if y_full == 1:
            continue

        u_full = ((1 + y_full) * pow(1 - y_full, _P25519 - 2, _P25519)) % _P25519
        rep_bytes = _elligator2_encode_u(u_full)
        if rep_bytes is None:
            continue

        u_full_bytes = u_full.to_bytes(32, "little")
        if elligator2_decode(rep_bytes) != u_full_bytes:
            raise RuntimeError("Elligator 2 编解码一致性自检异常")
        return ephemeral_private, u_full_bytes, rep_bytes


# ==================== 核心数学层：多进制分块换算 & 广义 n-EMD / 正交多进制 / 钻石编码 ====================

def required_digits_for_length(byte_len: int, profile: ModulationProfile) -> int:
    """计算指定字节数在给定调制档位下需要占用多少个 M 进制位（即多少个 n-像素通道组）"""
    full_blocks, rem = divmod(byte_len, profile.block_bytes)
    return full_blocks * profile.block_digits + profile.digits_for_bytes[rem]


ASYM_BOOT_GROUPS = required_digits_for_length(ASYM_BOOT_SIZE, HEADER_PROFILE)    # 48B -> 94 组 (752 通道)
SYM_BOOT_GROUPS = required_digits_for_length(SYM_BOOT_SIZE, HEADER_PROFILE)      # 16B -> 32 组 (256 通道)
META_GROUPS = required_digits_for_length(META_CIPHER_SIZE, HEADER_PROFILE)       # 26B -> 51 组 (408 通道)

ASYM_HEADER_CHANNELS = (ASYM_BOOT_GROUPS + META_GROUPS) * HEADER_PROFILE.group_size  # 145 * 8 = 1,160 通道
SYM_HEADER_CHANNELS = (SYM_BOOT_GROUPS + META_GROUPS) * HEADER_PROFILE.group_size    # 83 * 8  = 664 通道


def bytes_to_digits(data: bytes, profile: ModulationProfile) -> List[int]:
    """将任意字节流按档位最优分块无损转换为 M 进制数字列表 (0 .. radix-1)"""
    digits: List[int] = []
    b_size = profile.block_bytes
    radix = profile.radix
    d_table = profile.digits_for_bytes
    total = len(data)

    for offset in range(0, total, b_size):
        chunk = data[offset : offset + b_size]
        num_digits = d_table[len(chunk)]
        val = int.from_bytes(chunk, "big")
        chunk_digits = [0] * num_digits
        for idx in range(num_digits - 1, -1, -1):
            val, rem = divmod(val, radix)
            chunk_digits[idx] = rem
        digits.extend(chunk_digits)
    return digits


def digits_to_bytes(digits: Sequence[int], byte_len: int, profile: ModulationProfile) -> bytes:
    """将 M 进制数字列表按指定字节长度无损还原为原始字节流"""
    if byte_len == 0:
        return b""
    out = bytearray()
    digit_idx = 0
    remaining = byte_len
    b_size = profile.block_bytes
    radix = profile.radix
    d_table = profile.digits_for_bytes

    while remaining > 0:
        chunk_bytes = min(b_size, remaining)
        num_digits = d_table[chunk_bytes]
        val = 0
        for idx in range(digit_idx, digit_idx + num_digits):
            val = val * radix + digits[idx]
        if val >= (1 << (8 * chunk_bytes)):
            raise ValueError(f"{radix} 进制解码越界：未检测到有效隐写数据或密钥不匹配。")
        out.extend(val.to_bytes(chunk_bytes, "big"))
        digit_idx += num_digits
        remaining -= chunk_bytes
    return bytes(out)


def max_secret_capacity(
    total_channels: int, fixed_header_channels: int, profile: ModulationProfile
) -> int:
    """计算给定总通道数、固定头部开销与载荷调制档位下，最多可容纳多少字节压缩后载荷"""
    avail_channels = total_channels - fixed_header_channels
    if avail_channels <= 0:
        return 0
    avail_groups = avail_channels // profile.group_size
    if avail_groups <= 0:
        return 0

    full_blocks, rem_digits = divmod(avail_groups, profile.block_digits)
    rem_bytes = 0
    for b_len in range(profile.block_bytes - 1, 0, -1):
        if profile.digits_for_bytes[b_len] <= rem_digits:
            rem_bytes = b_len
            break
    max_cipher_bytes = full_blocks * profile.block_bytes + rem_bytes
    return max(0, max_cipher_bytes - GCM_TAG_SIZE)


def select_adaptive_profile(
    stored_payload_len: int,
    total_channels: int,
    fixed_header_channels: int,
    requested_profile: str = "auto",
) -> ModulationProfile:
    """全谱系动态负载率自适应选择器：优先挑选能容纳目标载荷的最低失真档位（auto 默认严守画质安全红线）"""
    if requested_profile != "auto":
        prof = PROFILE_BY_KEY[requested_profile]
        cap = max_secret_capacity(total_channels, fixed_header_channels, prof)
        if stored_payload_len > cap:
            max_prof = PROFILES_ORDERED[-1]
            max_cap = max_secret_capacity(total_channels, fixed_header_channels, max_prof)
            hint = (
                f"（提示：改用 --profile auto 或 {max_prof.key} 最高可容纳 {max_cap:,} 字节）"
                if max_cap >= stored_payload_len and prof.key != max_prof.key
                else ""
            )
            raise ValueError(
                f"数据超出 [{prof.key}] 档位容量上限！当前档位最多可容纳 {cap:,} 字节，"
                f"但压缩后待写入载荷为 {stored_payload_len:,} 字节。{hint}"
            )
        return prof

    for prof in AUTO_PROFILES:
        cap = max_secret_capacity(total_channels, fixed_header_channels, prof)
        if stored_payload_len <= cap:
            return prof

    # 超出 auto 安全画质上限（base5, ±2）时，检查显式应急档 base7 是否可容纳并给出明确引导
    max_auto_prof = AUTO_PROFILES[-1]
    max_auto_cap = max_secret_capacity(total_channels, fixed_header_channels, max_auto_prof)
    emg_prof = PROFILES_ORDERED[-1]
    emg_cap = max_secret_capacity(total_channels, fixed_header_channels, emg_prof)
    if not emg_prof.auto_eligible and stored_payload_len <= emg_cap:
        raise ValueError(
            f"数据超出自动选档画质安全上限！[{max_auto_prof.key}] 档最多容纳 {max_auto_cap:,} 字节，"
            f"而待写入载荷（压缩后）为 {stored_payload_len:,} 字节。"
            f"建议更换更高分辨率图片；若确需强行写入，可显式指定 --profile {emg_prof.key} "
            f"（最高容纳 {emg_cap:,} 字节，单通道最大振幅 ±{emg_prof.max_delta}）。"
        )
    raise ValueError(
        f"数据过大！即便启用极限显式应急档 ({emg_prof.key})，当前载体最多也只能容纳 {emg_cap:,} 字节，"
        f"而待写入载荷（压缩后）为 {stored_payload_len:,} 字节。请更换更高分辨率的载体图片。"
    )


def _gemd_modify_group(vals: Sequence[int], target_d: int) -> List[int]:
    """广义 n-像素 EMD (模 2n+1, 适用于 emd64/emd32/emd16/emd8/emd6/emd4/emd3/emd2) 嵌入算子，含 0/255 边界最小失真回退"""
    n = len(vals)
    mod = 2 * n + 1
    out = list(vals)
    cur = sum((idx + 1) * val for idx, val in enumerate(out)) % mod
    diff = (target_d - cur) % mod
    if diff == 0:
        return out

    if diff <= n:
        idx = diff - 1
        if out[idx] < 255:
            out[idx] += 1
            return out
    else:
        idx = mod - diff - 1
        if out[idx] > 0:
            out[idx] -= 1
            return out

    for i in range(n):
        for s1 in (-1, 1):
            if not (0 <= out[i] + s1 <= 255):
                continue
            rem = (diff - s1 * (i + 1)) % mod
            if rem == 0:
                out[i] += s1
                return out
            if rem <= n:
                j = rem - 1
                s2 = 1
            else:
                j = mod - rem - 1
                s2 = -1
            if j != i and 0 <= out[j] + s2 <= 255:
                out[i] += s1
                out[j] += s2
                return out
            if j == i and 0 <= out[i] + s1 + s2 <= 255:
                out[i] += s1 + s2
                return out

    if n == 2:
        p1, p2 = out[0], out[1]
        for d1, d2 in _PAIR_EMD_OFFSETS:
            np1, np2 = p1 + d1, p2 + d2
            if 0 <= np1 <= 255 and 0 <= np2 <= 255 and (np1 + 2 * np2) % 5 == target_d:
                return [np1, np2]

    for i in range(n):
        for s1 in (-1, 1):
            if not (0 <= out[i] + s1 <= 255):
                continue
            for j in range(i + 1, n):
                for s2 in (-1, 1):
                    if not (0 <= out[j] + s2 <= 255):
                        continue
                    rem = (diff - s1 * (i + 1) - s2 * (j + 1)) % mod
                    if rem <= n:
                        k, s3 = rem - 1, 1
                    else:
                        k, s3 = mod - rem - 1, -1
                    if k not in (i, j) and 0 <= out[k] + s3 <= 255:
                        out[i] += s1
                        out[j] += s2
                        out[k] += s3
                        return out

    raise RuntimeError("不可达异常：广义 n-EMD 边界搜索失败")


def _base_m_modify_channel(val: int, target_d: int, radix: int) -> int:
    """
    单通道奇数进制正交晶格调制算子（适用于 base3 / base5 / base7）：
      - 正常区间：单通道最大偏移严格控制在 ±(radix // 2) 内，MSE 与 L∞ 严格最优
      - 0/255 边界：向合法范围另一侧平移一个完整周期 radix，保证无溢出且失真最小
    """
    half = radix // 2
    diff = (target_d - (val % radix)) % radix
    if diff == 0:
        return val
    delta = diff if diff <= half else diff - radix
    new_val = val + delta
    if 0 <= new_val <= 255:
        return new_val
    return new_val + radix if new_val < 0 else new_val - radix


def _diamond13_modify_pair(p1: int, p2: int, target_d: int) -> List[int]:
    """双像素钻石编码 (Diamond Encoding, k=2, 模 13) 嵌入算子：f(p1, p2) = (p1 + 5 * p2) % 13"""
    diff = (target_d - (p1 + 5 * p2)) % 13
    if diff == 0:
        return [p1, p2]

    d1, d2 = _DE13_PRIMARY_DELTAS[diff]
    np1, np2 = p1 + d1, p2 + d2
    if 0 <= np1 <= 255 and 0 <= np2 <= 255:
        return [np1, np2]

    for bd1, bd2 in _DE13_BOUNDARY_OFFSETS:
        bp1, bp2 = p1 + bd1, p2 + bd2
        if 0 <= bp1 <= 255 and 0 <= bp2 <= 255:
            if (bp1 + 5 * bp2) % 13 == target_d:
                return [bp1, bp2]

    raise RuntimeError("不可达异常：钻石编码 (模 13) 边界搜索失败")


def modulate_group(vals: Sequence[int], target_d: int, profile: ModulationProfile) -> List[int]:
    """按指定档位对像素通道组执行模数调制"""
    if profile.kind == "base_m":
        return [_base_m_modify_channel(vals[0], target_d, profile.radix)]
    if profile.kind == "diamond13":
        return _diamond13_modify_pair(vals[0], vals[1], target_d)
    return _gemd_modify_group(vals, target_d)


def extract_group_digit(raw: bytes, group_positions: Sequence[int], profile: ModulationProfile) -> int:
    """按指定档位从像素通道组盲提取单个 M 进制数字"""
    if profile.kind == "base_m":
        return raw[group_positions[0]] % profile.radix
    if profile.kind == "diamond13":
        return (raw[group_positions[0]] + 5 * raw[group_positions[1]]) % 13
    total = 0
    for idx, pos in enumerate(group_positions):
        total += (idx + 1) * raw[pos]
    return total % profile.radix


# ==================== 载荷无损压缩层 ====================

def compress_payload(data: bytes, codec: str) -> Tuple[int, bytes]:
    """支持 none / gzip / bzip2 / xz 及自动择优 auto（绝不发生负压缩膨胀）"""
    if codec == "auto":
        candidates = [(CODEC_IDS["none"], data)]
        for name in ("gzip", "bzip2", "xz"):
            candidates.append(compress_payload(data, name))
        return min(candidates, key=lambda item: len(item[1]))
    if codec == "none":
        return CODEC_IDS["none"], data
    if codec == "gzip":
        return CODEC_IDS["gzip"], gzip.compress(data, compresslevel=9, mtime=0)
    if codec == "bzip2":
        return CODEC_IDS["bzip2"], bz2.compress(data, compresslevel=9)
    if codec == "xz":
        return CODEC_IDS["xz"], lzma.compress(data, format=lzma.FORMAT_XZ, preset=6)
    raise ValueError(f"不支持的压缩算法：{codec}")


def decompress_payload(data: bytes, codec_id: int) -> bytes:
    """按编码 ID 还原压缩载荷"""
    if codec_id not in ID_CODECS:
        raise ValueError("未知压缩编码标识，隐写数据已损坏。")
    codec = ID_CODECS[codec_id]
    try:
        if codec == "none":
            return data
        if codec == "gzip":
            return gzip.decompress(data)
        if codec == "bzip2":
            return bz2.decompress(data)
        return lzma.decompress(data, format=lzma.FORMAT_XZ)
    except Exception as exc:
        raise ValueError("解压隐写载荷失败：数据已损坏。") from exc


# ==================== CSPRNG 流式 n-元组洗牌与 ECIES 密码学层 ====================

def keystream(seed: bytes, domain: bytes, size: int) -> bytes:
    """基于 SHA-256 计数器模式的确定性密码学安全密钥流"""
    out = bytearray()
    counter = 0
    while len(out) < size:
        out.extend(hashlib.sha256(seed + domain + counter.to_bytes(8, "big")).digest())
        counter += 1
    return bytes(out[:size])


def mask_data(data: bytes, seed: bytes, domain: bytes) -> bytes:
    """对引导头执行流密码异或掩码，绑定接收方公钥与图像上下文"""
    stream = keystream(seed, domain, len(data))
    return bytes(val ^ mask for val, mask in zip(data, stream))


def position_stream(seed: bytes, pool_size: int, count: int) -> Iterator[int]:
    """基于 SHA-256 CSPRNG 的流式稀疏 Fisher-Yates 洗牌生成器"""
    if count > pool_size:
        raise ValueError("载体图片尺寸过小，可用像素通道不足。")
    swaps: Dict[int, int] = {}
    counter = 0
    buf = b""
    for idx in range(count):
        if len(buf) < 8:
            buf += hashlib.sha256(
                seed + STREAM_DOMAIN + counter.to_bytes(8, "big")
            ).digest()
            counter += 1
        rand_val = int.from_bytes(buf[:8], "big")
        buf = buf[8:]
        target = idx + rand_val % (pool_size - idx)

        val_i = swaps.pop(idx, idx)
        if idx == target:
            yield val_i
        else:
            selected = swaps.get(target, target)
            swaps[target] = val_i
            yield selected


def header_channel_groups(
    boot_seed: bytes, total_channels: int, group_count: int, group_size: int
) -> Tuple[List[Tuple[int, ...]], Set[int]]:
    """生成引导头专用的 n-像素通道组列表及保留通道集合"""
    needed = group_count * group_size
    flat = list(position_stream(boot_seed, total_channels, needed))
    groups = [
        tuple(flat[idx : idx + group_size]) for idx in range(0, needed, group_size)
    ]
    return groups, set(flat)


def iter_unreserved_positions(
    pos_seed: bytes, total_channels: int, reserved_set: Set[int]
) -> Iterator[int]:
    """跳过引导头保留通道后，流式产出互不冲突的可用通道索引流"""
    for pos in position_stream(pos_seed, total_channels, total_channels):
        if pos not in reserved_set:
            yield pos


def take_channel_groups(
    pos_iter: Iterator[int], group_size: int, group_count: int
) -> Iterator[Tuple[int, ...]]:
    """从连续的伪随机可用通道流中按指定 group_size 切片产出 group_count 个通道元组"""
    for _ in range(group_count):
        grp = tuple(next(pos_iter) for _ in range(group_size))
        yield grp


def image_context_bytes(size: Tuple[int, int], mode: str) -> bytes:
    """将图像宽高与通道模式编码为上下文绑定字节串"""
    mode_raw = mode.encode("ascii")
    return struct.pack(">IIB", size[0], size[1], len(mode_raw)) + mode_raw


def derive_public_seed(
    recipient_public_bytes: bytes, size: Tuple[int, int], mode: str
) -> bytes:
    """从接收方公钥与图像上下文派生引导头定位与掩码种子"""
    ctx = image_context_bytes(size, mode)
    return hashlib.sha256(PUBLIC_BOOT_DOMAIN + recipient_public_bytes + ctx).digest()


def derive_kdf_materials(
    shared_secret: bytes, salt: bytes, info: bytes
) -> Tuple[bytes, bytes, bytes, bytes, bytes]:
    """通过 HKDF-SHA256 域分离派生元数据密钥、载荷密钥、位置洗牌种子及两个 Nonce"""
    material = HKDF(
        algorithm=hashes.SHA256(),
        length=KEY_SIZE * 3 + NONCE_SIZE * 2,
        salt=salt,
        info=info,
    ).derive(shared_secret)
    meta_key = material[:KEY_SIZE]
    enc_key = material[KEY_SIZE : KEY_SIZE * 2]
    pos_seed = material[KEY_SIZE * 2 : KEY_SIZE * 3]
    meta_nonce = material[KEY_SIZE * 3 : KEY_SIZE * 3 + NONCE_SIZE]
    payload_nonce = material[KEY_SIZE * 3 + NONCE_SIZE :]
    return meta_key, enc_key, pos_seed, meta_nonce, payload_nonce


def derive_ecies_materials(
    shared_secret: bytes,
    salt: bytes,
    recipient_public_bytes: bytes,
    ephemeral_rep_bytes: bytes,
    ephemeral_u_bytes: bytes,
    size: Tuple[int, int],
    mode: str,
) -> Tuple[bytes, bytes, bytes, bytes, bytes]:
    """派生 X25519 + Elligator 2 ECIES 会话密钥材料"""
    info = (
        ECIES_KDF_DOMAIN
        + recipient_public_bytes
        + ephemeral_rep_bytes
        + ephemeral_u_bytes
        + image_context_bytes(size, mode)
    )
    return derive_kdf_materials(shared_secret, salt, info)


def pack_profile_codec_byte(profile_id: int, codec_id: int) -> int:
    """将自适应档位 ID (高 4 位, 0..15) 与压缩编码 ID (低 4 位) 紧凑编码为单字节"""
    return ((profile_id & 0x0F) << 4) | (codec_id & 0x0F)


def unpack_profile_codec_byte(packed: int) -> Tuple[int, int]:
    """从单字节解包出 (profile_id, codec_id)"""
    return (packed >> 4) & 0x0F, packed & 0x0F


# ==================== 原生图像元数据与 PNG 辅助块无痕透传层 ====================

_PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"


class CoverMetadataBundle:
    """
    载体图像元数据与色彩空间无痕克隆容器：
      - 若输入源本身为 PNG：在二进制块级精确捕获安全辅助块及相对 IDAT 位置；
      - 若输入源为 JPG / WebP / TIFF 等跨格式图像：自动提取 ICC Profile、EXIF 及 DPI 写入标准 PNG 块。
    """

    def __init__(
        self,
        source_format: Optional[str],
        mode_preserved: bool,
        raw_png_chunks: List[Tuple[bytes, bytes, bool]],
        fallback_info: Dict[str, Any],
    ) -> None:
        self.source_format = source_format or "UNKNOWN"
        self.mode_preserved = mode_preserved
        self.raw_png_chunks = raw_png_chunks
        self.fallback_info = fallback_info

    def summary_tags(self) -> List[str]:
        """返回已保留的元数据特征摘要标签，供终端日志审计展示"""
        tags: List[str] = []
        if self.raw_png_chunks:
            seen: List[str] = []
            for cid, _, _ in self.raw_png_chunks:
                name = cid.decode("latin1", errors="replace")
                if name not in seen:
                    seen.append(name)
            tags.extend(seen)
        else:
            if "icc_profile" in self.fallback_info:
                tags.append("iCCP(ICC色彩配置)")
            if "exif" in self.fallback_info:
                tags.append("eXIf(相机信息)")
            if "gamma" in self.fallback_info:
                tags.append("gAMA")
            if "dpi" in self.fallback_info:
                tags.append("pHYs(DPI)")
        return tags


def _extract_raw_png_ancillary_chunks(
    image_path: str, mode_preserved: bool
) -> List[Tuple[bytes, bytes, bool]]:
    """按标准 PNG 二进制格式无损提取所有安全的非关键辅助块及相对 IDAT 位置"""
    chunks_out: List[Tuple[bytes, bytes, bool]] = []
    seen_idat = False
    try:
        with open(image_path, "rb") as fp:
            if fp.read(8) != _PNG_SIGNATURE:
                return []
            while True:
                hdr = fp.read(8)
                if len(hdr) < 8:
                    break
                length, cid = struct.unpack(">I4s", hdr)
                if cid == b"IEND":
                    break
                if cid == b"IDAT":
                    seen_idat = True
                    fp.seek(length + 4, os.SEEK_CUR)
                    continue
                is_safe_sbit = (cid == b"sBIT") and mode_preserved
                if cid in _SAFE_PNG_ANCILLARY_CHUNKS or is_safe_sbit:
                    raw_data = fp.read(length)
                    if len(raw_data) != length:
                        break
                    fp.seek(4, os.SEEK_CUR)  # 跳过 4 字节 CRC32
                    chunks_out.append((cid, raw_data, seen_idat))
                else:
                    fp.seek(length + 4, os.SEEK_CUR)
    except Exception:
        return []
    return chunks_out


def _load_normalized_image(
    image_path: str, preserve_metadata: bool = True
) -> Tuple[Image.Image, Optional[CoverMetadataBundle]]:
    """
    加载载体图像，安全标准化为 8-bit L / RGB / RGBA 结构，并同步捕获色彩配置与辅助块元数据。
    特别修复 16-bit 灰度 PNG ("I;16" / "I") 直接 convert 会发生全白截断的隐患。
    """
    with Image.open(image_path) as src:
        orig_format = src.format
        orig_mode = src.mode

        fallback_info: Dict[str, Any] = {}
        if preserve_metadata:
            for key in ("icc_profile", "exif", "dpi", "gamma", "chromaticity", "srgb"):
                val = src.info.get(key)
                if val is not None:
                    fallback_info[key] = val
            if "exif" not in fallback_info:
                try:
                    exif_obj = src.getexif()
                    if exif_obj:
                        fallback_info["exif"] = exif_obj.tobytes()
                except Exception:
                    pass

        if orig_mode in ("RGB", "RGBA", "L"):
            norm_img = src.copy()
        elif orig_mode in ("I;16", "I;16B", "I;16L", "I"):
            norm_img = src.point(lambda px: min(255, max(0, int(px) >> 8))).convert("L")
        elif orig_mode in ("LA", "PA") or (orig_mode == "P" and "transparency" in src.info):
            norm_img = src.convert("RGBA")
        else:
            norm_img = src.convert("RGB")

        mode_preserved = norm_img.mode == orig_mode

    if not preserve_metadata:
        return norm_img, None

    raw_chunks: List[Tuple[bytes, bytes, bool]] = []
    if orig_format == "PNG":
        raw_chunks = _extract_raw_png_ancillary_chunks(image_path, mode_preserved)

    bundle = CoverMetadataBundle(
        source_format=orig_format,
        mode_preserved=mode_preserved,
        raw_png_chunks=raw_chunks,
        fallback_info=fallback_info,
    )
    return norm_img, bundle


def _pack_png_chunk(cid: bytes, data: bytes) -> bytes:
    """按标准 PNG 规范封装单个数据块（4 字节大端长度 + 4 字节类型码 + 数据 + 4 字节 CRC32）"""
    crc = zlib.crc32(cid)
    crc = zlib.crc32(data, crc) & 0xFFFFFFFF
    return struct.pack(">I4s", len(data), cid) + data + struct.pack(">I", crc)


def _inject_png_ancillary_chunks(
    base_png_bytes: bytes, raw_chunks: Sequence[Tuple[bytes, bytes, bool]]
) -> bytes:
    """
    将捕获的原图 PNG 安全辅助块按原始顺序无损注入编码后的 PNG 字节流：
      - after_idat=False 的块插入在 IHDR 之后、首个 IDAT 之前；
      - after_idat=True  的块插入在最后一个 IDAT 之后、IEND 之前。
    彻底绕过 Pillow PngInfo 对 iCCP / pHYs / eXIf / mDCV / cLLI 等标准公共块的静默过滤。
    """
    if not base_png_bytes.startswith(_PNG_SIGNATURE):
        return base_png_bytes

    pre_idat_blobs = [
        _pack_png_chunk(cid, data) for cid, data, after in raw_chunks if not after
    ]
    post_idat_blobs = [
        _pack_png_chunk(cid, data) for cid, data, after in raw_chunks if after
    ]

    out = bytearray(_PNG_SIGNATURE)
    pos = 8
    total_len = len(base_png_bytes)
    pre_written = False
    post_written = False

    while pos + 8 <= total_len:
        length, cid = struct.unpack_from(">I4s", base_png_bytes, pos)
        chunk_end = pos + 12 + length
        if chunk_end > total_len:
            break
        raw_chunk_slice = base_png_bytes[pos:chunk_end]

        if cid == b"IDAT" and not pre_written:
            for blob in pre_idat_blobs:
                out.extend(blob)
            pre_written = True
            out.extend(raw_chunk_slice)
        elif cid == b"IEND":
            if not pre_written:
                for blob in pre_idat_blobs:
                    out.extend(blob)
                pre_written = True
            if not post_written:
                for blob in post_idat_blobs:
                    out.extend(blob)
                post_written = True
            out.extend(raw_chunk_slice)
        else:
            out.extend(raw_chunk_slice)

        pos = chunk_end

    return bytes(out)


def _save_stego_png(
    stego_img: Image.Image,
    output_path: str,
    meta_bundle: Optional[CoverMetadataBundle],
) -> List[str]:
    """将隐写后的像素矩阵连同原图元数据/PNG辅助块无损封装写入目标 PNG 文件"""
    if meta_bundle is None:
        stego_img.save(output_path, format="PNG", optimize=True)
        return []

    if meta_bundle.raw_png_chunks:
        buf = io.BytesIO()
        stego_img.save(buf, format="PNG", optimize=True)
        patched_png = _inject_png_ancillary_chunks(
            buf.getvalue(), meta_bundle.raw_png_chunks
        )
        Path(output_path).write_bytes(patched_png)
        return meta_bundle.summary_tags()

    save_kwargs: Dict[str, Any] = {"format": "PNG", "optimize": True}
    f_info = meta_bundle.fallback_info
    if "icc_profile" in f_info and f_info["icc_profile"]:
        save_kwargs["icc_profile"] = f_info["icc_profile"]
    if "exif" in f_info and f_info["exif"]:
        save_kwargs["exif"] = f_info["exif"]
    if "dpi" in f_info and f_info["dpi"]:
        save_kwargs["dpi"] = f_info["dpi"]

    pnginfo_extra = PngImagePlugin.PngInfo()
    has_extra = False
    if "gamma" in f_info and isinstance(f_info["gamma"], (int, float)):
        gamma_int = int(round(float(f_info["gamma"]) * 100000))
        pnginfo_extra.add(b"gAMA", struct.pack(">I", gamma_int))
        has_extra = True
    if has_extra:
        save_kwargs["pnginfo"] = pnginfo_extra

    stego_img.save(output_path, **save_kwargs)
    return meta_bundle.summary_tags()


def compute_psnr(orig_raw: bytes, stego_raw: bytes) -> float:
    """计算载体与隐写图像之间的精确峰值信噪比 (PSNR, dB)；存在 NumPy 时自动向量化加速"""
    if not orig_raw or orig_raw == stego_raw:
        return float("inf")
    if np is not None:
        arr_a = np.frombuffer(orig_raw, dtype=np.uint8).astype(np.int32)
        arr_b = np.frombuffer(stego_raw, dtype=np.uint8).astype(np.int32)
        diff = arr_a - arr_b
        mse = float(np.mean(diff * diff))
        if mse == 0.0:
            return float("inf")
        return 10.0 * math.log10((255.0 * 255.0) / mse)

    mv_a = memoryview(orig_raw)
    mv_b = memoryview(stego_raw)
    sq_err = 0
    for idx in range(len(mv_a)):
        diff_v = mv_a[idx] - mv_b[idx]
        if diff_v:
            sq_err += diff_v * diff_v
    if sq_err == 0:
        return float("inf")
    mse = sq_err / float(len(mv_a))
    return 10.0 * math.log10((255.0 * 255.0) / mse)


# ==================== 自适应 ECIES 隐写与盲提取核心执行层 ====================

def _embed_adaptive_streams(
    raw: bytearray,
    boot_digits: Sequence[int],
    boot_groups: Sequence[Tuple[int, ...]],
    meta_digits: Sequence[int],
    body_digits: Sequence[int],
    pos_iter: Iterator[int],
    body_profile: ModulationProfile,
) -> Tuple[int, int]:
    """两阶段混合精度嵌入执行器：固定头部 (emd8) + 全谱系自适应载荷主体 (emd64 .. base7)"""
    header_modified = 0
    body_modified = 0

    for target_d, grp in zip(boot_digits, boot_groups):
        orig = [raw[p] for p in grp]
        updated = modulate_group(orig, target_d, HEADER_PROFILE)
        for pos, old_v, new_v in zip(grp, orig, updated):
            if new_v != old_v:
                raw[pos] = new_v
                header_modified += 1

    for target_d, grp in zip(
        meta_digits,
        take_channel_groups(pos_iter, HEADER_PROFILE.group_size, len(meta_digits)),
    ):
        orig = [raw[p] for p in grp]
        updated = modulate_group(orig, target_d, HEADER_PROFILE)
        for pos, old_v, new_v in zip(grp, orig, updated):
            if new_v != old_v:
                raw[pos] = new_v
                header_modified += 1

    for target_d, grp in zip(
        body_digits,
        take_channel_groups(pos_iter, body_profile.group_size, len(body_digits)),
    ):
        orig = [raw[p] for p in grp]
        updated = modulate_group(orig, target_d, body_profile)
        for pos, old_v, new_v in zip(grp, orig, updated):
            if new_v != old_v:
                raw[pos] = new_v
                body_modified += 1

    return header_modified, body_modified


def embed_data_ecies(
    cover_path: str,
    output_path: str,
    secret_data: bytes,
    recipient_public_bytes: bytes,
    codec: str = "auto",
    profile_mode: str = "auto",
    preserve_metadata: bool = True,
) -> dict:
    """使用接收方 X25519 公钥 + 全群 Elligator 2 隐匿 + 元数据无痕透传保存为无损 PNG"""
    if not str(output_path).lower().endswith(".png"):
        raise ValueError("输出文件必须以 .png 结尾，防止有损压缩破坏像素模余数！")
    if len(recipient_public_bytes) != EPHEMERAL_PUBLIC_SIZE:
        raise ValueError("接收方 X25519 公钥长度无效（应为 32 字节）。")

    img, meta_bundle = _load_normalized_image(cover_path, preserve_metadata=preserve_metadata)
    orig_bytes = img.tobytes()
    raw = bytearray(orig_bytes)
    total_channels = len(raw)

    codec_id, stored_payload = compress_payload(secret_data, codec)
    chosen_prof = select_adaptive_profile(
        len(stored_payload), total_channels, ASYM_HEADER_CHANNELS, profile_mode
    )
    prof_max_cap = max_secret_capacity(total_channels, ASYM_HEADER_CHANNELS, chosen_prof)

    recipient_public = x25519.X25519PublicKey.from_public_bytes(recipient_public_bytes)
    ephemeral_private, ephemeral_u_bytes, ephemeral_rep_bytes = generate_elligator2_ephemeral()
    shared_secret = ephemeral_private.exchange(recipient_public)

    salt = os.urandom(SALT_SIZE)
    boot_header = ephemeral_rep_bytes + salt

    meta_key, enc_key, pos_seed, meta_nonce, payload_nonce = derive_ecies_materials(
        shared_secret,
        salt,
        recipient_public_bytes,
        ephemeral_rep_bytes,
        ephemeral_u_bytes,
        img.size,
        img.mode,
    )

    cipher_len = len(stored_payload) + GCM_TAG_SIZE
    prof_codec_byte = pack_profile_codec_byte(chosen_prof.prof_id, codec_id)
    meta_plain = (
        MAGIC
        + bytes([FORMAT_VERSION, prof_codec_byte])
        + struct.pack(">I", cipher_len)
    )
    meta_cipher = AESGCM(meta_key).encrypt(meta_nonce, meta_plain, boot_header)
    payload_cipher = AESGCM(enc_key).encrypt(
        payload_nonce, stored_payload, boot_header + meta_plain
    )

    pub_seed = derive_public_seed(recipient_public_bytes, img.size, img.mode)
    masked_boot = mask_data(boot_header, pub_seed, MASK_DOMAIN)

    boot_digits = bytes_to_digits(masked_boot, HEADER_PROFILE)
    meta_digits = bytes_to_digits(meta_cipher, HEADER_PROFILE)
    body_digits = bytes_to_digits(payload_cipher, chosen_prof)

    boot_groups, reserved_set = header_channel_groups(
        pub_seed, total_channels, ASYM_BOOT_GROUPS, HEADER_PROFILE.group_size
    )
    pos_iter = iter_unreserved_positions(pos_seed, total_channels, reserved_set)
    header_mod, body_mod = _embed_adaptive_streams(
        raw, boot_digits, boot_groups, meta_digits, body_digits, pos_iter, chosen_prof
    )

    stego_raw_bytes = bytes(raw)
    stego_img = Image.frombytes(img.mode, img.size, stego_raw_bytes)
    preserved_tags = _save_stego_png(stego_img, output_path, meta_bundle)
    psnr_db = compute_psnr(orig_bytes, stego_raw_bytes)

    body_used_channels = len(body_digits) * chosen_prof.group_size
    used_channels = ASYM_HEADER_CHANNELS + body_used_channels
    modified_channels = header_mod + body_mod
    return {
        "mode": "ecies-x25519-elligator2",
        "profile_key": chosen_prof.key,
        "profile_title": chosen_prof.title,
        "group_size": chosen_prof.group_size,
        "radix": chosen_prof.radix,
        "max_delta": chosen_prof.max_delta,
        "expected_mod_rate": chosen_prof.expected_mod_rate,
        "image_size": img.size,
        "image_mode": img.mode,
        "secret_bytes": len(secret_data),
        "stored_bytes": len(stored_payload),
        "codec": ID_CODECS[codec_id],
        "max_capacity": prof_max_cap,
        "total_channels": total_channels,
        "used_channels": used_channels,
        "modified_channels": modified_channels,
        "mod_rate_in_used": (modified_channels / used_channels * 100.0) if used_channels else 0.0,
        "body_mod_rate": (body_mod / body_used_channels * 100.0) if body_used_channels else 0.0,
        "overall_img_mod_rate": (modified_channels / total_channels * 100.0) if total_channels else 0.0,
        "psnr_db": psnr_db,
        "preserved_metadata": preserved_tags,
    }


def extract_data_ecies(
    stego_path: str,
    recipient_private_bytes: bytes,
    expected_public_bytes: Optional[bytes],
) -> Tuple[bytes, ModulationProfile]:
    """使用接收方 X25519 私钥盲提取并认证解密 PNG 中的隐写数据（全自动识别 12 档调制档位）"""
    if len(recipient_private_bytes) != KEY_SIZE:
        raise ValueError("接收方 X25519 私钥长度无效（应为 32 字节）。")

    recipient_private = x25519.X25519PrivateKey.from_private_bytes(recipient_private_bytes)
    recipient_public_bytes = serialize_x25519_public(recipient_private.public_key())
    if expected_public_bytes is not None and recipient_public_bytes != expected_public_bytes:
        raise ValueError("提取脚本中的公私钥对校验不一致，文件可能已损坏！")

    with Image.open(stego_path) as src:
        if src.mode not in ("RGB", "RGBA", "L"):
            raise ValueError(f"不支持的图像模式 {src.mode}，请确认输入的是原始隐写 PNG 文件。")
        img_size = src.size
        img_mode = src.mode
        raw = src.tobytes()

    total_channels = len(raw)
    max_cap_prof = PROFILES_ORDERED[-1]
    min_body_ch = required_digits_for_length(GCM_TAG_SIZE, max_cap_prof) * max_cap_prof.group_size
    if total_channels < ASYM_HEADER_CHANNELS + min_body_ch:
        raise ValueError("图片尺寸过小，不可能包含有效的自适应 EMD 隐写数据。")

    pub_seed = derive_public_seed(recipient_public_bytes, img_size, img_mode)
    boot_groups, reserved_set = header_channel_groups(
        pub_seed, total_channels, ASYM_BOOT_GROUPS, HEADER_PROFILE.group_size
    )
    boot_digits = [extract_group_digit(raw, grp, HEADER_PROFILE) for grp in boot_groups]

    auth_err_msg = (
        "未找到匹配的隐写数据：请确认使用了正确的配对提取脚本/私钥，"
        "且 PNG 图片在传输中未遭压缩、缩放或篡改！"
    )
    try:
        masked_boot = digits_to_bytes(boot_digits, ASYM_BOOT_SIZE, HEADER_PROFILE)
    except ValueError:
        raise ValueError(auth_err_msg) from None

    boot_header = mask_data(masked_boot, pub_seed, MASK_DOMAIN)
    ephemeral_rep_bytes = boot_header[:EPHEMERAL_PUBLIC_SIZE]
    salt = boot_header[EPHEMERAL_PUBLIC_SIZE:]

    ephemeral_u_bytes = elligator2_decode(ephemeral_rep_bytes)
    try:
        ephemeral_public = x25519.X25519PublicKey.from_public_bytes(ephemeral_u_bytes)
        shared_secret = recipient_private.exchange(ephemeral_public)
    except ValueError:
        raise ValueError(auth_err_msg) from None

    meta_key, enc_key, pos_seed, meta_nonce, payload_nonce = derive_ecies_materials(
        shared_secret,
        salt,
        recipient_public_bytes,
        ephemeral_rep_bytes,
        ephemeral_u_bytes,
        img_size,
        img_mode,
    )

    pos_iter = iter_unreserved_positions(pos_seed, total_channels, reserved_set)
    meta_digits = [
        extract_group_digit(raw, grp, HEADER_PROFILE)
        for grp in take_channel_groups(pos_iter, HEADER_PROFILE.group_size, META_GROUPS)
    ]
    try:
        meta_cipher = digits_to_bytes(meta_digits, META_CIPHER_SIZE, HEADER_PROFILE)
        meta_plain = AESGCM(meta_key).decrypt(meta_nonce, meta_cipher, boot_header)
    except (ValueError, InvalidTag):
        raise ValueError(auth_err_msg) from None

    if len(meta_plain) != META_PLAIN_SIZE or meta_plain[:4] != MAGIC:
        raise ValueError(auth_err_msg)

    version = meta_plain[4]
    prof_id, codec_id = unpack_profile_codec_byte(meta_plain[5])
    (cipher_len,) = struct.unpack(">I", meta_plain[6:10])

    if (
        version != FORMAT_VERSION
        or prof_id not in PROFILE_BY_ID
        or codec_id not in ID_CODECS
        or cipher_len < GCM_TAG_SIZE
    ):
        raise ValueError("隐写协议版本不兼容或头部数据已损坏。")

    body_profile = PROFILE_BY_ID[prof_id]
    body_groups_count = required_digits_for_length(cipher_len, body_profile)
    needed_channels = ASYM_HEADER_CHANNELS + body_groups_count * body_profile.group_size
    if needed_channels > total_channels:
        raise ValueError("隐写数据长度异常或图片已损坏。")

    body_digits = [
        extract_group_digit(raw, grp, body_profile)
        for grp in take_channel_groups(pos_iter, body_profile.group_size, body_groups_count)
    ]
    payload_cipher = digits_to_bytes(body_digits, cipher_len, body_profile)

    try:
        stored_payload = AESGCM(enc_key).decrypt(
            payload_nonce, payload_cipher, boot_header + meta_plain
        )
    except InvalidTag:
        raise ValueError("载荷 AES-GCM 认证失败：图片部分像素可能已被篡改！") from None

    return decompress_payload(stored_payload, codec_id), body_profile
# === [PAIR_SHARED_CORE_END] ===


# ==================== 升级版对称口令自适应模式（随机盐引导 + 元数据无痕透传） ====================

PBKDF2_BOOT_ITER = 100_000      # 对称引导头定位种子迭代次数
PBKDF2_MASTER_ITER = 200_000    # 对称主密钥派生迭代次数


def _derive_symmetric_boot_seed(
    password: str, size: Tuple[int, int], mode: str
) -> bytes:
    """从口令与图像上下文派生对称引导盐的定位与掩码种子"""
    salt_ctx = SYM_BOOT_DOMAIN + image_context_bytes(size, mode)
    return hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), salt_ctx, PBKDF2_BOOT_ITER, dklen=KEY_SIZE
    )


def _derive_symmetric_materials(
    password: str, boot_salt: bytes, size: Tuple[int, int], mode: str
) -> Tuple[bytes, bytes, bytes, bytes, bytes]:
    """结合随机引导盐派生每次独立的主密钥、载荷位置种子与 Nonce"""
    master_secret = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), boot_salt, PBKDF2_MASTER_ITER, dklen=KEY_SIZE
    )
    info = SYM_KDF_DOMAIN + image_context_bytes(size, mode)
    return derive_kdf_materials(master_secret, boot_salt, info)


def embed_data(
    cover_path: str,
    output_path: str,
    secret_data: bytes,
    password: str,
    codec: str = "auto",
    profile_mode: str = "auto",
    preserve_metadata: bool = True,
) -> dict:
    """对称口令模式：通过随机盐引导 + 双层 AES-256-GCM + 元数据无痕透传自适应隐写"""
    if not str(output_path).lower().endswith(".png"):
        raise ValueError("输出文件必须以 .png 结尾，防止有损压缩破坏像素模余数！")
    if not password:
        raise ValueError("密码不能为空！")

    img, meta_bundle = _load_normalized_image(cover_path, preserve_metadata=preserve_metadata)
    orig_bytes = img.tobytes()
    raw = bytearray(orig_bytes)
    total_channels = len(raw)

    codec_id, stored_payload = compress_payload(secret_data, codec)
    chosen_prof = select_adaptive_profile(
        len(stored_payload), total_channels, SYM_HEADER_CHANNELS, profile_mode
    )
    prof_max_cap = max_secret_capacity(total_channels, SYM_HEADER_CHANNELS, chosen_prof)

    boot_salt = os.urandom(SYM_BOOT_SIZE)
    boot_seed = _derive_symmetric_boot_seed(password, img.size, img.mode)
    masked_boot = mask_data(boot_salt, boot_seed, MASK_DOMAIN)

    meta_key, enc_key, pos_seed, meta_nonce, payload_nonce = _derive_symmetric_materials(
        password, boot_salt, img.size, img.mode
    )

    cipher_len = len(stored_payload) + GCM_TAG_SIZE
    prof_codec_byte = pack_profile_codec_byte(chosen_prof.prof_id, codec_id)
    meta_plain = (
        MAGIC
        + bytes([FORMAT_VERSION, prof_codec_byte])
        + struct.pack(">I", cipher_len)
    )
    meta_cipher = AESGCM(meta_key).encrypt(meta_nonce, meta_plain, boot_salt)
    payload_cipher = AESGCM(enc_key).encrypt(
        payload_nonce, stored_payload, boot_salt + meta_plain
    )

    boot_digits = bytes_to_digits(masked_boot, HEADER_PROFILE)
    meta_digits = bytes_to_digits(meta_cipher, HEADER_PROFILE)
    body_digits = bytes_to_digits(payload_cipher, chosen_prof)

    boot_groups, reserved_set = header_channel_groups(
        boot_seed, total_channels, SYM_BOOT_GROUPS, HEADER_PROFILE.group_size
    )
    pos_iter = iter_unreserved_positions(pos_seed, total_channels, reserved_set)
    header_mod, body_mod = _embed_adaptive_streams(
        raw, boot_digits, boot_groups, meta_digits, body_digits, pos_iter, chosen_prof
    )

    stego_raw_bytes = bytes(raw)
    stego_img = Image.frombytes(img.mode, img.size, stego_raw_bytes)
    preserved_tags = _save_stego_png(stego_img, output_path, meta_bundle)
    psnr_db = compute_psnr(orig_bytes, stego_raw_bytes)

    body_used_channels = len(body_digits) * chosen_prof.group_size
    used_channels = SYM_HEADER_CHANNELS + body_used_channels
    modified_channels = header_mod + body_mod
    return {
        "mode": "symmetric-password",
        "profile_key": chosen_prof.key,
        "profile_title": chosen_prof.title,
        "group_size": chosen_prof.group_size,
        "radix": chosen_prof.radix,
        "max_delta": chosen_prof.max_delta,
        "expected_mod_rate": chosen_prof.expected_mod_rate,
        "image_size": img.size,
        "image_mode": img.mode,
        "secret_bytes": len(secret_data),
        "stored_bytes": len(stored_payload),
        "codec": ID_CODECS[codec_id],
        "max_capacity": prof_max_cap,
        "total_channels": total_channels,
        "used_channels": used_channels,
        "modified_channels": modified_channels,
        "mod_rate_in_used": (modified_channels / used_channels * 100.0) if used_channels else 0.0,
        "body_mod_rate": (body_mod / body_used_channels * 100.0) if body_used_channels else 0.0,
        "overall_img_mod_rate": (modified_channels / total_channels * 100.0) if total_channels else 0.0,
        "psnr_db": psnr_db,
        "preserved_metadata": preserved_tags,
    }


def extract_data(stego_path: str, password: str) -> Tuple[bytes, ModulationProfile]:
    """对称口令模式：从含隐写的 PNG 图片中盲提取并认证解密原始数据"""
    if not password:
        raise ValueError("密码不能为空！")

    with Image.open(stego_path) as src:
        if src.mode not in ("RGB", "RGBA", "L"):
            raise ValueError(f"不支持的图像模式 {src.mode}，请确认输入的是原始隐写 PNG 文件。")
        img_size = src.size
        img_mode = src.mode
        raw = src.tobytes()

    total_channels = len(raw)
    max_cap_prof = PROFILES_ORDERED[-1]
    min_body_ch = required_digits_for_length(GCM_TAG_SIZE, max_cap_prof) * max_cap_prof.group_size
    if total_channels < SYM_HEADER_CHANNELS + min_body_ch:
        raise ValueError("图片尺寸过小，不可能包含有效的自适应 EMD 隐写数据。")

    boot_seed = _derive_symmetric_boot_seed(password, img_size, img_mode)
    boot_groups, reserved_set = header_channel_groups(
        boot_seed, total_channels, SYM_BOOT_GROUPS, HEADER_PROFILE.group_size
    )
    boot_digits = [extract_group_digit(raw, grp, HEADER_PROFILE) for grp in boot_groups]

    auth_err_msg = "提取失败：密码错误，或图片未包含有效隐写数据 / 已遭有损压缩修改！"
    try:
        masked_boot = digits_to_bytes(boot_digits, SYM_BOOT_SIZE, HEADER_PROFILE)
    except ValueError:
        raise ValueError(auth_err_msg) from None

    boot_salt = mask_data(masked_boot, boot_seed, MASK_DOMAIN)
    meta_key, enc_key, pos_seed, meta_nonce, payload_nonce = _derive_symmetric_materials(
        password, boot_salt, img_size, img_mode
    )

    pos_iter = iter_unreserved_positions(pos_seed, total_channels, reserved_set)
    meta_digits = [
        extract_group_digit(raw, grp, HEADER_PROFILE)
        for grp in take_channel_groups(pos_iter, HEADER_PROFILE.group_size, META_GROUPS)
    ]
    try:
        meta_cipher = digits_to_bytes(meta_digits, META_CIPHER_SIZE, HEADER_PROFILE)
        meta_plain = AESGCM(meta_key).decrypt(meta_nonce, meta_cipher, boot_salt)
    except (ValueError, InvalidTag):
        raise ValueError(auth_err_msg) from None

    if len(meta_plain) != META_PLAIN_SIZE or meta_plain[:4] != MAGIC:
        raise ValueError(auth_err_msg)

    version = meta_plain[4]
    prof_id, codec_id = unpack_profile_codec_byte(meta_plain[5])
    (cipher_len,) = struct.unpack(">I", meta_plain[6:10])
    if (
        version != FORMAT_VERSION
        or prof_id not in PROFILE_BY_ID
        or codec_id not in ID_CODECS
        or cipher_len < GCM_TAG_SIZE
    ):
        raise ValueError("隐写协议版本不兼容或头部数据已损坏。")

    body_profile = PROFILE_BY_ID[prof_id]
    body_groups_count = required_digits_for_length(cipher_len, body_profile)
    needed_channels = SYM_HEADER_CHANNELS + body_groups_count * body_profile.group_size
    if needed_channels > total_channels:
        raise ValueError(auth_err_msg)

    body_digits = [
        extract_group_digit(raw, grp, body_profile)
        for grp in take_channel_groups(pos_iter, body_profile.group_size, body_groups_count)
    ]
    payload_cipher = digits_to_bytes(body_digits, cipher_len, body_profile)

    try:
        stored_payload = AESGCM(enc_key).decrypt(
            payload_nonce, payload_cipher, boot_salt + meta_plain
        )
    except InvalidTag:
        raise ValueError("载荷 AES-GCM 认证失败：图片像素可能已被篡改！") from None

    return decompress_payload(stored_payload, codec_id), body_profile


# ==================== 重装加固版配对脚本生成器与 AST 控制流/字节码混淆器 ====================

import ast
import base64
import builtins
import marshal
import random
import string
import tempfile

PAIR_EMBED_ROLE_CODE = r'''
def main():
    parser = argparse.ArgumentParser(
        description=f"全谱系 12 档自适应广义 n-EMD / 正交多进制 / 钻石编码 + X25519 Elligator 2 公钥配对隐写嵌入脚本（配对 ID：{PAIR_ID}）"
    )
    parser.add_argument("-c", "--cover", required=True, help="输入载体图片路径（支持 PNG/JPG/BMP/WebP/16-bit PNG 等）")
    parser.add_argument("-o", "--output", help="输出隐写 PNG 图片路径（嵌入时必填，须以 .png 结尾）")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("-m", "--message", help="要隐藏的 UTF-8 文本消息")
    group.add_argument("-f", "--file", help="要隐藏的任意文件路径")
    group.add_argument("--capacity", action="store_true", help="查看当前载体图片在全谱系 12 档下的最大容量与元数据状态")
    parser.add_argument(
        "--profile",
        choices=PROFILE_CHOICES,
        default="auto",
        help="隐写调制档位：auto（默认在 emd64..base5 间自动择优最低失真）或手动指定具体档位（含显式应急档 base7）",
    )
    parser.add_argument(
        "--compress",
        choices=("auto", "none", "gzip", "bzip2", "xz"),
        default="auto",
        help="隐写前无损压缩策略：auto（默认自动择优）/ none / gzip / bzip2 / xz",
    )
    parser.add_argument(
        "--strip-metadata",
        action="store_true",
        help="主动剥离原图 EXIF / ICC Profile / PNG 辅助块（默认无痕保留原图色彩与元数据块）",
    )
    args = parser.parse_args()

    try:
        if args.capacity:
            img, meta_bundle = _load_normalized_image(args.cover, preserve_metadata=True)
            channels = len(img.tobytes())
            meta_tags = meta_bundle.summary_tags() if meta_bundle else []
            meta_desc = ", ".join(meta_tags) if meta_tags else "无额外辅助块"
            print(f"[*] 配对 ID    : {PAIR_ID}")
            print(f"[*] 图像尺寸   : {img.size[0]} x {img.size[1]} ({img.mode}) | 可用通道数: {channels:,}")
            print(f"[*] 原图元数据 : {meta_desc}")
            for prof in PROFILES_ORDERED:
                cap = max_secret_capacity(channels, ASYM_HEADER_CHANNELS, prof)
                tag = "auto" if prof.auto_eligible else "显式"
                print(
                    f"    - [{prof.key:<5}|{tag}] {prof.title:<34} : {cap:>10,} 字节 "
                    f"({cap / 1024:>8.2f} KB | 修改率 ~{prof.expected_mod_rate:>5.2f}% | ±{prof.max_delta})"
                )
            return

        if not args.output:
            parser.error("执行嵌入操作时必须通过 -o / --output 指定输出 .png 路径。")

        secret_bytes = (
            args.message.encode("utf-8")
            if args.message is not None
            else Path(args.file).read_bytes()
        )
        pub_key_material = _reconstruct_public_key()
        stats = embed_data_ecies(
            args.cover,
            args.output,
            secret_bytes,
            pub_key_material,
            args.compress,
            args.profile,
            preserve_metadata=not args.strip_metadata,
        )
        usage_pct = (stats["stored_bytes"] / stats["max_capacity"] * 100) if stats["max_capacity"] else 100.0
        psnr_str = f"{stats['psnr_db']:.2f} dB" if math.isfinite(stats["psnr_db"]) else "∞ (零修改)"
        meta_str = ", ".join(stats["preserved_metadata"]) if stats["preserved_metadata"] else "无 / 已剥离"
        print(f"[+] 全谱系自适应隐写（Elligator 2 公钥模式）成功！已保存至: {args.output}")
        print(f"    配对 ID  : {PAIR_ID}")
        print(f"    启用档位 : [{stats['profile_key']}] {stats['profile_title']} (最大振幅 ±{stats['max_delta']})")
        print(
            f"    载荷大小 : 原始 {stats['secret_bytes']:,} 字节 -> 压缩后 {stats['stored_bytes']:,} 字节 "
            f"(算法: {stats['codec']}，占当前档位容量 {usage_pct:.2f}%)"
        )
        print(
            f"    通道统计 : 使用 {stats['used_channels']:,} / {stats['total_channels']:,} 个通道，"
            f"实际仅修改 {stats['modified_channels']:,} 个通道"
        )
        print(
            f"    隐蔽指标 : 载荷区修改率 {stats['body_mod_rate']:.2f}% (理论期望 ~{stats['expected_mod_rate']:.2f}%) | "
            f"全图修改率 {stats['overall_img_mod_rate']:.4f}% | 图像质量 PSNR: {psnr_str}"
        )
        print(f"    无痕克隆 : 已透传保留块 [{meta_str}]")
    except Exception as exc:
        print(f"[-] 错误: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
'''

PAIR_EXTRACT_ROLE_CODE = r'''
def main():
    parser = argparse.ArgumentParser(
        description=f"全谱系 12 档自适应广义 n-EMD / 正交多进制 / 钻石编码 + X25519 Elligator 2 私钥配对盲提取脚本（配对 ID：{PAIR_ID}）"
    )
    parser.add_argument("-i", "--input", required=True, help="含隐写的 PNG 图片路径")
    parser.add_argument("-o", "--output", help="输出还原文件路径（不指定则尝试按 UTF-8 文本打印）")
    args = parser.parse_args()

    try:
        priv_key_material = _reconstruct_private_key()
        pub_key_material = _reconstruct_public_key()
        recovered, prof = extract_data_ecies(
            args.input,
            priv_key_material,
            pub_key_material,
        )
        if args.output:
            Path(args.output).write_bytes(recovered)
            print(
                f"[+] 盲提取成功（配对 ID: {PAIR_ID} | 自动识别档位: {prof.key}）！"
                f"已还原 {len(recovered):,} 字节至: {args.output}"
            )
        else:
            try:
                text = recovered.decode("utf-8")
                print(
                    f"[+] 盲提取成功（配对 ID: {PAIR_ID} | 自动识别档位: [{prof.key}] {prof.title}），"
                    f"隐藏文本内容：\n{text}"
                )
            except UnicodeDecodeError:
                print(
                    f"[!] 盲提取成功（共 {len(recovered):,} 字节，档位: {prof.key}），"
                    f"但内容为二进制数据而非 UTF-8 文本，请使用 -o 参数保存到文件。"
                )
    except Exception as exc:
        print(f"[-] 错误: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
'''


def _build_split_key_function_source(
    func_name: str, secret_bytes: bytes, rng: random.Random
) -> str:
    """
    密钥代数秘密分片生成器（消除明文 Hex 字符串与静态连续字节特征）：
      将 32 字节公/私钥拆分为 4 组独立的 256-bit 掩码分片 S0 ^ S1 ^ S2 ^ S3 = Key，
      再按 32-bit 无符号字重排加上旋转偏移，编译期不出现任何原始密钥字节串或 bytes.fromhex 调用。
    """
    if len(secret_bytes) != 32:
        raise ValueError("分片密钥长度必须为 32 字节。")

    shares = [[rng.randrange(256) for _ in range(32)] for _ in range(3)]
    final_share = [
        secret_bytes[i] ^ shares[0][i] ^ shares[1][i] ^ shares[2][i]
        for i in range(32)
    ]
    shares.append(final_share)

    masks = [rng.randrange(1, 0x7FFFFFFF) for _ in range(8)]
    encoded_rows: List[List[int]] = []
    for row in shares:
        words = [
            (int.from_bytes(bytes(row[col * 4 : (col + 1) * 4]), "big") + masks[col]) & 0xFFFFFFFF
            for col in range(8)
        ]
        encoded_rows.append(words)

    rng.shuffle(encoded_rows)

    lines = [
        f"def {func_name}():",
        f"    _m = {masks!r}",
        f"    _t = {encoded_rows!r}",
        "    _acc = [0] * 8",
        "    for _row in _t:",
        "        for _idx in range(8):",
        "            _w = (_row[_idx] - _m[_idx]) & 0xFFFFFFFF",
        "            _acc[_idx] ^= _w",
        "    _out = bytearray()",
        "    for _val in _acc:",
        "        _out.extend(_val.to_bytes(4, 'big'))",
        "    return bytes(_out)",
    ]
    return "\n".join(lines) + "\n"


class _TypeAnnotationStripper(ast.NodeTransformer):
    """剥离类型注解与 typing 导入，消除静态类型签名"""

    def visit_ImportFrom(self, node: ast.ImportFrom):
        if node.module == "typing":
            return None
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef):
        node.returns = None
        self.generic_visit(node)
        return node

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef):
        node.returns = None
        self.generic_visit(node)
        return node

    def visit_arg(self, node: ast.arg):
        node.annotation = None
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign):
        if node.value is None:
            return None
        return ast.Assign(targets=[node.target], value=self.visit(node.value))


class _YieldOrScopeDetector(ast.NodeVisitor):
    """检测函数体内是否含 yield/async/global/nonlocal，以筛选可安全执行状态机平坦化的函数"""

    def __init__(self) -> None:
        self.has_generator_or_special = False

    def visit_Yield(self, node: ast.Yield) -> None:
        self.has_generator_or_special = True

    def visit_YieldFrom(self, node: ast.YieldFrom) -> None:
        self.has_generator_or_special = True

    def visit_Await(self, node: ast.Await) -> None:
        self.has_generator_or_special = True

    def visit_Global(self, node: ast.Global) -> None:
        self.has_generator_or_special = True

    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        self.has_generator_or_special = True

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        return

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        return


class _ControlFlowHardener(ast.NodeTransformer):
    """
    AST 控制流平坦化与不透明谓词转换器：
      1. 将顺序执行的函数顶层语句切分为多个随机编号的基本块；
      2. 包裹进 `while _st != STOP:` 状态机循环，物理打乱代码块排列顺序；
      3. 在分发器中插入基于数论恒等式（如 `(x*(x+1)) & 1 == 1` 恒为 False）的虚假死代码分支。
    """

    def __init__(self, rng: random.Random, create_name) -> None:
        self.rng = rng
        self.create_name = create_name

    @staticmethod
    def _strip_docstring_stmt(body: List[ast.stmt]) -> List[ast.stmt]:
        if (
            body
            and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)
        ):
            return body[1:]
        return body

    def _make_bogus_block(self, state_var: str, stop_state: int) -> Tuple[ast.expr, List[ast.stmt]]:
        """构造代数不透明恒假谓词分支：连续整数乘积 n*(n+1) 必为偶数，最低位永远不可能为 1"""
        seed_num = self.rng.randrange(0x1000, 0x7FFFFF)
        opaque_var = self.create_name()
        cond = ast.Compare(
            left=ast.BinOp(
                left=ast.BinOp(
                    left=ast.Name(id=state_var, ctx=ast.Load()),
                    op=ast.Mult(),
                    right=ast.BinOp(
                        left=ast.Name(id=state_var, ctx=ast.Load()),
                        op=ast.Add(),
                        right=ast.Constant(value=1),
                    ),
                ),
                op=ast.BitAnd(),
                right=ast.Constant(value=1),
            ),
            ops=[ast.Eq()],
            comparators=[ast.Constant(value=1)],
        )
        bogus_stmts: List[ast.stmt] = [
            ast.Assign(
                targets=[ast.Name(id=opaque_var, ctx=ast.Store())],
                value=ast.BinOp(
                    left=ast.Name(id=state_var, ctx=ast.Load()),
                    op=ast.BitXor(),
                    right=ast.Constant(value=seed_num),
                ),
            ),
            ast.Assign(
                targets=[ast.Name(id=state_var, ctx=ast.Store())],
                value=ast.Constant(value=stop_state),
            ),
        ]
        return cond, bogus_stmts

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)

        detector = _YieldOrScopeDetector()
        for stmt in node.body:
            detector.visit(stmt)
        if detector.has_generator_or_special:
            return node

        clean_body = self._strip_docstring_stmt(node.body)
        if len(clean_body) < 3 or len(clean_body) > 28:
            node.body = clean_body or [ast.Pass()]
            return node

        chunks: List[List[ast.stmt]] = []
        idx = 0
        while idx < len(clean_body):
            step = 1 if len(clean_body) <= 8 else self.rng.choice((1, 2))
            chunks.append(clean_body[idx : idx + step])
            idx += step

        if len(chunks) < 3:
            node.body = clean_body
            return node

        state_var = self.create_name()
        used_ids: Set[int] = set()

        def _alloc_state() -> int:
            while True:
                sid = self.rng.randrange(0x10000, 0x7FFFFFFF)
                if sid not in used_ids:
                    used_ids.add(sid)
                    return sid

        state_ids = [_alloc_state() for _ in range(len(chunks))]
        stop_state = _alloc_state()

        dispatch_blocks: List[Tuple[ast.expr, List[ast.stmt]]] = []
        for pos, block_stmts in enumerate(chunks):
            cur_id = state_ids[pos]
            next_id = state_ids[pos + 1] if pos + 1 < len(chunks) else stop_state
            cond = ast.Compare(
                left=ast.Name(id=state_var, ctx=ast.Load()),
                ops=[ast.Eq()],
                comparators=[ast.Constant(value=cur_id)],
            )
            patched_stmts = list(block_stmts)
            if not isinstance(patched_stmts[-1], (ast.Return, ast.Raise)):
                patched_stmts.append(
                    ast.Assign(
                        targets=[ast.Name(id=state_var, ctx=ast.Store())],
                        value=ast.Constant(value=next_id),
                    )
                )
            dispatch_blocks.append((cond, patched_stmts))

        for _ in range(self.rng.choice((1, 2))):
            dispatch_blocks.append(self._make_bogus_block(state_var, stop_state))
        self.rng.shuffle(dispatch_blocks)

        if_chain: Optional[ast.If] = None
        for cond, stmts in reversed(dispatch_blocks):
            if if_chain is None:
                else_stop: List[ast.stmt] = [
                    ast.Assign(
                        targets=[ast.Name(id=state_var, ctx=ast.Store())],
                        value=ast.Constant(value=stop_state),
                    )
                ]
                if_chain = ast.If(test=cond, body=stmts, orelse=else_stop)
            else:
                if_chain = ast.If(test=cond, body=stmts, orelse=[if_chain])

        init_assign = ast.Assign(
            targets=[ast.Name(id=state_var, ctx=ast.Store())],
            value=ast.Constant(value=state_ids[0]),
        )
        while_loop = ast.While(
            test=ast.Compare(
                left=ast.Name(id=state_var, ctx=ast.Load()),
                ops=[ast.NotEq()],
                comparators=[ast.Constant(value=stop_state)],
            ),
            body=[if_chain],  # type: ignore[list-item]
            orelse=[],
        )
        node.body = [init_assign, while_loop]
        return node


class _NameCollector(ast.NodeVisitor):
    """收集语法树中所有可安全重命名的标识符（排除属性名以避免破坏标准库/第三方库方法调用）"""

    def __init__(self) -> None:
        self.names: Set[str] = set()
        self.attr_names: Set[str] = set()
        self.kw_names: Set[str] = set()

    def visit_Attribute(self, node: ast.Attribute) -> None:
        self.attr_names.add(node.attr)
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        for kw in node.keywords:
            if kw.arg is not None:
                self.kw_names.add(kw.arg)
        self.generic_visit(node)

    def visit_Name(self, node: ast.Name) -> None:
        self.names.add(node.id)

    def visit_arg(self, node: ast.arg) -> None:
        self.names.add(node.arg)
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.names.add(node.name)
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self.names.add(node.name)
        self.generic_visit(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.names.add(node.name)
        self.generic_visit(node)

    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if node.name:
            self.names.add(node.name)
        self.generic_visit(node)

    def visit_Global(self, node: ast.Global) -> None:
        self.names.update(node.names)

    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        self.names.update(node.names)


class _SourceObfuscator(ast.NodeTransformer):
    """AST 常量与标识符深度混淆器：标识符随机化、多态字节/字符串异或掩码、多元算术整数拆分"""

    def __init__(self, name_map: dict, rng: random.Random, decoder_name: str) -> None:
        self.name_map = name_map
        self.rng = rng
        self.decoder_name = decoder_name

    @staticmethod
    def _strip_docstring(node) -> None:
        if (
            node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
            and isinstance(node.body[0].value.value, str)
        ):
            node.body.pop(0)

    def _rename(self, name: str) -> str:
        return self.name_map.get(name, name)

    def _decode_call(self, value):
        raw = value.encode("utf-8") if isinstance(value, str) else value
        key_len = self.rng.randint(12, 24)
        key = bytes(self.rng.randrange(256) for _ in range(key_len))
        stride = self.rng.randrange(1, 255) | 1
        encoded = bytes(
            (byte ^ key[(idx * stride) % key_len] ^ (idx & 0xFF)) & 0xFF
            for idx, byte in enumerate(raw)
        )
        call = ast.Call(
            func=ast.Name(id=self.decoder_name, ctx=ast.Load()),
            args=[ast.Constant(encoded), ast.Constant(key), ast.Constant(stride)],
            keywords=[],
        )
        if isinstance(value, str):
            call = ast.Call(
                func=ast.Attribute(value=call, attr="decode", ctx=ast.Load()),
                args=[],
                keywords=[],
            )
        return call

    def visit_Module(self, node: ast.Module):
        self._strip_docstring(node)
        self.generic_visit(node)
        return node

    def visit_Name(self, node: ast.Name):
        node.id = self._rename(node.id)
        return node

    def visit_arg(self, node: ast.arg):
        node.arg = self._rename(node.arg)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self._strip_docstring(node)
        node.name = self._rename(node.name)
        self.generic_visit(node)
        return node

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef):
        self._strip_docstring(node)
        node.name = self._rename(node.name)
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node: ast.ClassDef):
        self._strip_docstring(node)
        node.name = self._rename(node.name)
        self.generic_visit(node)
        return node

    def visit_Call(self, node: ast.Call):
        node.func = self.visit(node.func)
        node.args = [self.visit(arg) for arg in node.args]
        for kw in node.keywords:
            if kw.arg is not None:
                kw.arg = self._rename(kw.arg)
            kw.value = self.visit(kw.value)
        return node

    def visit_Import(self, node: ast.Import):
        for alias in node.names:
            bound_name = alias.asname or alias.name.partition(".")[0]
            if bound_name in self.name_map:
                alias.asname = self.name_map[bound_name]
        return node

    def visit_ImportFrom(self, node: ast.ImportFrom):
        for alias in node.names:
            bound_name = alias.asname or alias.name
            if bound_name in self.name_map:
                alias.asname = self.name_map[bound_name]
        return node

    def visit_ExceptHandler(self, node: ast.ExceptHandler):
        if node.name:
            node.name = self._rename(node.name)
        self.generic_visit(node)
        return node

    def visit_Global(self, node: ast.Global):
        node.names = [self._rename(name) for name in node.names]
        return node

    def visit_Nonlocal(self, node: ast.Nonlocal):
        node.names = [self._rename(name) for name in node.names]
        return node

    def visit_JoinedStr(self, node: ast.JoinedStr):
        """将 f-string 统一改写为加密模板 .format(...) 调用，隐藏全部提示文本特征"""
        template: List[str] = []
        args: List[ast.AST] = []
        conv_map = {115: "!s", 114: "!r", 97: "!a"}

        for part in node.values:
            if isinstance(part, ast.Constant) and isinstance(part.value, str):
                template.append(part.value.replace("{", "{{").replace("}", "}}"))
            elif isinstance(part, ast.FormattedValue):
                conv = conv_map.get(part.conversion, "")
                spec = ""
                if part.format_spec is not None:
                    if isinstance(part.format_spec, ast.JoinedStr) and all(
                        isinstance(seg, ast.Constant) and isinstance(seg.value, str)
                        for seg in part.format_spec.values
                    ):
                        spec = ":" + "".join(
                            seg.value for seg in part.format_spec.values  # type: ignore[attr-defined]
                        )
                    else:
                        part.value = self.visit(part.value)
                        return node
                template.append("{" + conv + spec + "}")
                args.append(self.visit(part.value))
            else:
                return node

        template_call = self._decode_call("".join(template))
        return ast.Call(
            func=ast.Attribute(value=template_call, attr="format", ctx=ast.Load()),
            args=args,
            keywords=[],
        )

    def visit_Constant(self, node: ast.Constant):
        value = node.value
        if isinstance(value, (str, bytes)):
            return self._decode_call(value)
        if isinstance(value, int) and not isinstance(value, bool):
            mask_a = self.rng.randrange(1, 1 << 29)
            mask_b = self.rng.randrange(1, 1 << 20)
            if self.rng.randrange(2) == 0:
                return ast.BinOp(
                    left=ast.BinOp(
                        left=ast.Constant((value + mask_b) ^ mask_a),
                        op=ast.BitXor(),
                        right=ast.Constant(mask_a),
                    ),
                    op=ast.Sub(),
                    right=ast.Constant(mask_b),
                )
            return ast.BinOp(
                left=ast.BinOp(
                    left=ast.Constant((value - mask_b) ^ mask_a),
                    op=ast.BitXor(),
                    right=ast.Constant(mask_a),
                ),
                op=ast.Add(),
                right=ast.Constant(mask_b),
            )
        return node


def _random_name_factory(rng: random.Random):
    """生成高混淆视觉相似标识符（前缀随机搭配易混淆字母数字组合）"""
    used: Set[str] = set()
    head_chars = "IlO_"
    tail_chars = "Il1O0_" + string.ascii_letters

    def create() -> str:
        while True:
            length = rng.randint(12, 17)
            name = "_" + rng.choice(head_chars) + "".join(rng.choice(tail_chars) for _ in range(length))
            if name not in used:
                used.add(name)
                return name

    return create


def _decoder_source(decoder_name: str, create_name) -> str:
    data_name = create_name()
    key_name = create_name()
    stride_name = create_name()
    idx_name = create_name()
    val_name = create_name()
    klen_name = create_name()
    return (
        f"def {decoder_name}({data_name}, {key_name}, {stride_name}):\n"
        f"    {klen_name} = len({key_name})\n"
        f"    return bytes(({val_name} ^ {key_name}[({idx_name} * {stride_name}) % {klen_name}] ^ ({idx_name} & 255)) & 255 "
        f"for {idx_name}, {val_name} in enumerate({data_name}))\n"
    )


def _obfuscate_source(source: str) -> str:
    """
    多层重装加固编译管线：
      Stage 1: 剥离类型注解与文档字符串
      Stage 2: 核心函数 AST 控制流平坦化（状态机乱序跳转 + 不透明恒假谓词注入）
      Stage 3: 全局符号随机化 + 多态步进流密码字符串加密 + 多元算术整数拆分
      Stage 4: 直接编译为 Python Code Object 并 Marshal 序列化（不保留任何明文 Python 源码字符串）
      Stage 5: zlib 紧缩 + PBKDF2-HMAC-SHA256 派生流加密 + 多段乱序分块 Base85 自校验加载壳
    """
    rng = random.SystemRandom()
    create_name = _random_name_factory(rng)

    tree = ast.parse(source)
    tree = _TypeAnnotationStripper().visit(tree)
    tree = _ControlFlowHardener(rng, create_name).visit(tree)
    ast.fix_missing_locations(tree)

    collector = _NameCollector()
    collector.visit(tree)
    reserved = set(dir(builtins)) | collector.attr_names | collector.kw_names
    names = {
        name
        for name in collector.names
        if name not in reserved and not (name.startswith("__") and name.endswith("__"))
    }
    name_map = {name: create_name() for name in sorted(names)}

    decoder_name = create_name()
    decoder_ast = ast.parse(_decoder_source(decoder_name, create_name)).body[0]
    tree.body.insert(0, decoder_ast)
    tree = _SourceObfuscator(name_map, rng, decoder_name).visit(tree)
    ast.fix_missing_locations(tree)

    obf_source_str = ast.unparse(tree)
    code_obj = compile(obf_source_str, "<emd_shielded_core>", "exec")
    marshaled_code = marshal.dumps(code_obj)
    compressed_blob = zlib.compress(marshaled_code, level=9)

    loader_salt = os.urandom(16)
    loader_pepper = os.urandom(16)
    kdf_iters = rng.randint(2048, 3072)
    stream_key = hashlib.pbkdf2_hmac(
        "sha256", loader_pepper, loader_salt, kdf_iters, dklen=len(compressed_blob)
    )
    encrypted_blob = bytes(a ^ b for a, b in zip(compressed_blob, stream_key))
    digest_tag = hashlib.sha256(encrypted_blob + loader_salt).digest()[:8]

    b85_raw = base64.b85encode(encrypted_blob).decode("ascii")
    slice_count = 6
    step_len = max(1, (len(b85_raw) + slice_count - 1) // slice_count)
    ordered_parts = [b85_raw[i : i + step_len] for i in range(0, len(b85_raw), step_len)]
    indexed_parts = list(enumerate(ordered_parts))
    rng.shuffle(indexed_parts)

    perm_order = [orig_idx for orig_idx, _ in indexed_parts]
    shuffled_chunks = [part for _, part in indexed_parts]
    restore_indices = [perm_order.index(i) for i in range(len(shuffled_chunks))]

    b64_alias = create_name()
    hl_alias = create_name()
    ms_alias = create_name()
    zl_alias = create_name()
    fn_boot = create_name()
    v_parts = create_name()
    v_order = create_name()
    v_raw = create_name()
    v_key = create_name()

    parts_literal = "[\n" + "".join(f"        {seg!r},\n" for seg in shuffled_chunks) + "    ]"
    loader = (
        "#!/usr/bin/env python3\n"
        "# -*- coding: utf-8 -*-\n"
        f"# Python Bytecode Version Bound: {sys.version_info.major}.{sys.version_info.minor}\n"
        f"import base64 as {b64_alias}, hashlib as {hl_alias}, marshal as {ms_alias}, zlib as {zl_alias}\n"
        f"def {fn_boot}():\n"
        f"    {v_parts} = {parts_literal}\n"
        f"    {v_order} = {restore_indices!r}\n"
        f"    {v_raw} = {b64_alias}.b85decode(''.join({v_parts}[i] for i in {v_order}))\n"
        f"    if {hl_alias}.sha256({v_raw} + {loader_salt!r}).digest()[:8] != {digest_tag!r}:\n"
        f"        raise RuntimeError('Integrity check failed')\n"
        f"    {v_key} = {hl_alias}.pbkdf2_hmac('sha256', {loader_pepper!r}, {loader_salt!r}, {kdf_iters}, dklen=len({v_raw}))\n"
        f"    return {ms_alias}.loads({zl_alias}.decompress(bytes(a ^ b for a, b in zip({v_raw}, {v_key}))))\n"
        f"exec({fn_boot}(), globals())\n"
    )
    compile(loader, "<obfuscated_pair_loader>", "exec")
    return loader


def _extract_shared_core_source() -> str:
    """从当前脚本文件中提取共享核心层代码"""
    script_path = Path(__file__).resolve()
    full_text = script_path.read_text(encoding="utf-8")
    start_tag = "# === [PAIR_SHARED_CORE_START] ==="
    end_tag = "# === [PAIR_SHARED_CORE_END] ==="
    start_idx = full_text.find(start_tag)
    end_idx = full_text.find(end_tag)
    if start_idx < 0 or end_idx < 0 or end_idx <= start_idx:
        raise RuntimeError("未找到核心模板标记，无法生成配对脚本。")
    return full_text[start_idx + len(start_tag) : end_idx].strip()


def render_pair_script(
    pair_id: str,
    public_hex: str,
    role_code: str,
    private_hex: Optional[str] = None,
    obfuscate: bool = True,
) -> str:
    """组装并渲染嵌入端或提取端独立脚本（密钥全程采用 4 路异或代数分片嵌入，零 Hex 明文特征）"""
    rng = random.SystemRandom()
    public_bytes = bytes.fromhex(public_hex)
    fingerprint = hashlib.sha256(public_bytes).hexdigest()

    banner = (
        "#!/usr/bin/env python3\n"
        "# -*- coding: utf-8 -*-\n"
        f"# 自动生成的全谱系 12 档自适应广义 n-EMD / 正交多进制 / 钻石编码 + X25519 Elligator 2 配对隐写脚本 | 配对 ID: {pair_id}\n"
        f"# 接收方公钥指纹 (SHA-256): {fingerprint}\n\n"
    )

    key_builders = [
        f"\nPAIR_ID = {pair_id!r}\n",
        _build_split_key_function_source("_reconstruct_public_key", public_bytes, rng),
    ]
    if private_hex is not None:
        private_bytes = bytes.fromhex(private_hex)
        key_builders.append(
            _build_split_key_function_source("_reconstruct_private_key", private_bytes, rng)
        )

    core_source = _extract_shared_core_source()
    raw_source = banner + core_source + "\n" + "\n".join(key_builders) + "\n" + role_code.lstrip()
    compile(raw_source, "<pair_script_template>", "exec")
    return _obfuscate_source(raw_source) if obfuscate else raw_source


def generate_pair(
    output_dir: Path, prefix: str = "emd", obfuscate: bool = True
) -> Tuple[Path, Path, str, str]:
    """生成一对唯一绑定 X25519 公私钥的全谱系自适应隐写嵌入脚本与提取脚本"""
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    recipient_private = x25519.X25519PrivateKey.generate()
    private_bytes = recipient_private.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )
    public_bytes = serialize_x25519_public(recipient_private.public_key())

    public_hex = public_bytes.hex()
    private_hex = private_bytes.hex()
    fingerprint = hashlib.sha256(public_bytes).hexdigest()
    pair_id = fingerprint[:16]

    embed_path = output_dir / f"{prefix}_embed_{pair_id}.py"
    extract_path = output_dir / f"{prefix}_extract_{pair_id}.py"
    for path in (embed_path, extract_path):
        if path.exists():
            raise FileExistsError(f"拒绝覆盖已存在的文件：{path}")

    embed_src = render_pair_script(
        pair_id, public_hex, PAIR_EMBED_ROLE_CODE, private_hex=None, obfuscate=obfuscate
    )
    extract_src = render_pair_script(
        pair_id, public_hex, PAIR_EXTRACT_ROLE_CODE, private_hex=private_hex, obfuscate=obfuscate
    )

    with embed_path.open("x", encoding="utf-8", newline="\n") as f_emb:
        f_emb.write(embed_src)
    with extract_path.open("x", encoding="utf-8", newline="\n") as f_ext:
        f_ext.write(extract_src)

    if os.name == "posix":
        embed_path.chmod(0o755)
        extract_path.chmod(0o600)

    return embed_path, extract_path, pair_id, fingerprint


# ==================== 数学、全谱系 12 档边界、元数据透传与混淆脚本实机执行自检套件 ====================

def run_selftest() -> None:
    """验证 Elligator 2、全谱系 12 档极值边界、11 档自动跳档、base7 红线拦截、元数据透传及混淆脚本实机闭环"""
    import subprocess

    print("[*] 1/6 正在验证随机 32 字节噪点的 Elligator 2 曲线点映射与 Cofactor-8 ECDH 一致性...")
    recipient_priv = x25519.X25519PrivateKey.generate()
    recipient_pub = recipient_priv.public_key()
    for _ in range(32):
        noise = os.urandom(32)
        u = int.from_bytes(elligator2_decode(noise), "little")
        rhs = (u * (u * u + _A25519 * u + 1)) % _P25519
        if rhs != 0 and pow(rhs, _P25519_HALF, _P25519) != 1:
            raise RuntimeError("自检失败：随机噪点解码未落在合法 Curve25519 曲线上！")

        eph_priv, eph_u_bytes, eph_rep_bytes = generate_elligator2_ephemeral()
        if elligator2_decode(eph_rep_bytes) != eph_u_bytes:
            raise RuntimeError("自检失败：Elligator 2 代表元解码结果不一致！")
        if eph_priv.exchange(recipient_pub) != recipient_priv.exchange(
            x25519.X25519PublicKey.from_public_bytes(eph_u_bytes)
        ):
            raise RuntimeError("自检失败：收发双方 X25519 共享密钥不一致！")
    print("    [OK] Elligator 2 全群随机代表元与 X25519 ECDH 密钥协商 100% 通过。")

    print("[*] 2/6 正在验证全谱系 12 档调制算子 (emd64 .. base7) 在 0/255 极值边界下的完备性...")
    boundary_patterns = [0, 1, 2, 3, 128, 252, 253, 254, 255]
    for prof in PROFILES_ORDERED:
        for fill_v in boundary_patterns:
            base_grp = [fill_v] * prof.group_size
            checker_grp = [0 if idx % 2 == 0 else 255 for idx in range(prof.group_size)]
            for sample_grp in (base_grp, checker_grp):
                for target_d in range(prof.radix):
                    mod_grp = modulate_group(sample_grp, target_d, prof)
                    if any(not (0 <= v <= 255) for v in mod_grp):
                        raise RuntimeError(f"自检失败：{prof.key} 出现像素通道溢出！")
                    buf = bytes(mod_grp)
                    ext_d = extract_group_digit(buf, list(range(prof.group_size)), prof)
                    if ext_d != target_d:
                        raise RuntimeError(f"自检失败：{prof.key} 边界调制还原不一致！")
    print(f"    [OK] 全部 {len(PROFILES_ORDERED)} 档极值边界无溢出与盲提取还原测试 100% 通过。")

    priv_bytes = recipient_priv.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )
    pub_bytes = serialize_x25519_public(recipient_pub)

    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_root = Path(tmp_dir)
        cover_file = tmp_root / "cover_meta.png"
        w, h = 80, 80
        total_ch = w * h * 3
        cover_bytes = bytearray(os.urandom(total_ch))
        cover_bytes[0:24] = b"\x00\xff" * 12

        src_pnginfo = PngImagePlugin.PngInfo()
        src_pnginfo.add(b"gAMA", struct.pack(">I", 45455))
        src_pnginfo.add_text("Software", "CameraRaw-Pro-Profile")
        src_pnginfo.add_itxt("Description", "测试广色域与 UTF-8 元数据无痕透传")
        dummy_icc = b"MOCK_ICC_PROFILE_DATA_" + os.urandom(32)
        Image.frombytes("RGB", (w, h), bytes(cover_bytes)).save(
            cover_file, format="PNG", pnginfo=src_pnginfo, icc_profile=dummy_icc, dpi=(300, 300)
        )

        print("[*] 3/6 正在验证 11 档 --profile auto 连续阶梯跳档与 base7 显式应急档安全红线...")
        prev_cap = 0
        for prof in AUTO_PROFILES:
            cur_cap = max_secret_capacity(total_ch, ASYM_HEADER_CHANNELS, prof)
            payload_size = max(16, (prev_cap + cur_cap) // 2)
            stego_file = tmp_root / f"stego_{prof.key}.png"
            secret_blob = os.urandom(payload_size)
            stats = embed_data_ecies(
                str(cover_file), str(stego_file), secret_blob, pub_bytes, "none", "auto"
            )
            if stats["profile_key"] != prof.key:
                raise RuntimeError(
                    f"自适应选档偏离预期：大小 {payload_size}B 期望 {prof.key}，实际 {stats['profile_key']}"
                )
            recovered, rec_prof = extract_data_ecies(str(stego_file), priv_bytes, pub_bytes)
            if recovered != secret_blob or rec_prof.key != prof.key:
                raise RuntimeError(f"自检失败：{prof.key} 档位盲提取还原数据不一致！")
            print(
                f"    [OK] 载荷 {payload_size:>4} B -> 自动选用 [{stats['profile_key']:<5}] "
                f"| 修改率: {stats['body_mod_rate']:5.2f}% | PSNR: {stats['psnr_db']:5.2f} dB"
            )
            prev_cap = cur_cap

        # 验证 base7 显式应急档：auto 必须拒绝超画质红线载荷，显式指定 base7 必须成功嵌入并盲提取还原
        emg_prof = PROFILE_BY_KEY["base7"]
        emg_cap = max_secret_capacity(total_ch, ASYM_HEADER_CHANNELS, emg_prof)
        emg_size = (prev_cap + emg_cap) // 2
        emg_blob = os.urandom(emg_size)
        emg_file = tmp_root / "stego_base7.png"
        try:
            embed_data_ecies(str(cover_file), str(emg_file), emg_blob, pub_bytes, "none", "auto")
            raise RuntimeError("自检失败：auto 模式未拦截超出画质安全红线的 base7 载荷！")
        except ValueError:
            pass
        emg_stats = embed_data_ecies(
            str(cover_file), str(emg_file), emg_blob, pub_bytes, "none", "base7"
        )
        emg_rec, emg_rec_prof = extract_data_ecies(str(emg_file), priv_bytes, pub_bytes)
        if emg_rec != emg_blob or emg_rec_prof.key != "base7":
            raise RuntimeError("自检失败：base7 显式应急档盲提取还原不一致！")
        print(
            f"    [OK] 载荷 {emg_size:>4} B -> auto 安全拦截，显式 [base7] 成功 "
            f"| 修改率: {emg_stats['body_mod_rate']:5.2f}% | PSNR: {emg_stats['psnr_db']:5.2f} dB"
        )

        print("[*] 4/6 正在验证图像元数据（ICC Profile / DPI / PNG 辅助块）无痕透传与可选剥离...")
        stego_check = tmp_root / "stego_emd64.png"
        with Image.open(stego_check) as chk_img:
            if chk_img.info.get("icc_profile") != dummy_icc:
                raise RuntimeError("自检失败：隐写后 ICC 色彩配置文件丢失或损坏！")
            if chk_img.info.get("Software") != "CameraRaw-Pro-Profile":
                raise RuntimeError("自检失败：隐写后 PNG tEXt 辅助块丢失！")
            if chk_img.info.get("Description") != "测试广色域与 UTF-8 元数据无痕透传":
                raise RuntimeError("自检失败：隐写后 PNG iTXt 国际化块丢失！")
            if "dpi" not in chk_img.info:
                raise RuntimeError("自检失败：隐写后 pHYs (DPI) 块丢失！")

        stripped_file = tmp_root / "stego_stripped.png"
        embed_data_ecies(
            str(cover_file), str(stripped_file), b"strip-test", pub_bytes, "auto", "auto", preserve_metadata=False
        )
        with Image.open(stripped_file) as strp_img:
            if "icc_profile" in strp_img.info or "Software" in strp_img.info:
                raise RuntimeError("自检失败：--strip-metadata 未能彻底剥离原图元数据！")
        print("    [OK] PNG iCCP / pHYs / gAMA / tEXt / iTXt 原样透传及 --strip-metadata 剥离测试 100% 通过。")

        print("[*] 5/6 正在验证对称口令模式闭环与无隐写图片安全拒绝...")
        sym_stego = tmp_root / "stego_sym.png"
        sym_secret = "全谱系 12 档自适应广义 EMD 对称口令微隐写测试 🚀".encode("utf-8") * 4
        sym_stats = embed_data(str(cover_file), str(sym_stego), sym_secret, "Str0ng#Pass!", "auto", "auto")
        sym_rec, sym_prof = extract_data(str(sym_stego), "Str0ng#Pass!")
        if sym_rec != sym_secret or sym_prof.key != sym_stats["profile_key"]:
            raise RuntimeError("自检失败：对称模式提取结果不一致！")

        try:
            extract_data_ecies(str(cover_file), priv_bytes, pub_bytes)
            raise RuntimeError("自检失败：无隐写载体图未触发认证拒绝！")
        except ValueError:
            pass
        print(f"    [OK] 对称口令自适应隐写（自动选用 [{sym_prof.key}]）闭环与非隐写图拒绝校验全部通过。")

        print("[*] 6/6 正在验证重装加固配对脚本（密钥分片 + AST 控制流平坦化 + Marshal 加密壳）端到端实机运行...")
        emb_script, ext_script, _, _ = generate_pair(tmp_root, prefix="testpair", obfuscate=True)
        emb_text = emb_script.read_text(encoding="utf-8")
        ext_text = ext_script.read_text(encoding="utf-8")
        if pub_bytes.hex()[:16] in emb_text or priv_bytes.hex()[:16] in ext_text or "fromhex" in ext_text:
            raise RuntimeError("自检失败：混淆后的配对脚本仍残留十六进制密钥特征！")

        pair_stego = tmp_root / "pair_e2e.png"
        e2e_msg = "v3.3 全谱系 12 档控制流平坦化与分片密钥配对提取实测成功！🔐"
        sub_env = os.environ.copy()
        sub_env["PYTHONUTF8"] = "1"
        sub_env["PYTHONIOENCODING"] = "utf-8"

        res_emb = subprocess.run(
            [sys.executable, str(emb_script), "-c", str(cover_file), "-o", str(pair_stego), "-m", e2e_msg],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=sub_env,
        )
        if res_emb.returncode != 0:
            raise RuntimeError(
                f"混淆嵌入脚本执行失败 (exit={res_emb.returncode})：\n"
                f"--- STDOUT ---\n{res_emb.stdout}\n--- STDERR ---\n{res_emb.stderr}"
            )

        res_ext = subprocess.run(
            [sys.executable, str(ext_script), "-i", str(pair_stego)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=sub_env,
        )
        if res_ext.returncode != 0:
            raise RuntimeError(
                f"混淆提取脚本执行失败 (exit={res_ext.returncode})：\n"
                f"--- STDOUT ---\n{res_ext.stdout}\n--- STDERR ---\n{res_ext.stderr}"
            )
        if e2e_msg not in res_ext.stdout:
            raise RuntimeError(f"自检失败：混淆配对脚本实机提取输出不匹配：{res_ext.stdout}")

    print("    [OK] 混淆配对脚本静态零密钥残留校验与子进程实机嵌入/盲提取闭环 100% 通过。")
    print("\n[+] 全部 6 项密码学、全谱系 12 档边界、元数据透传与 AST 控制流平坦化工程自检 100% 通过！您可放心使用。")


# ==================== 密钥辅助解析与主命令行工具入口 ====================

def _parse_key_input(key_arg: str, label: str) -> bytes:
    """支持直接传入 64 位十六进制密钥字符串，或传入密钥文件路径"""
    cleaned = key_arg.strip()
    if len(cleaned) == 64:
        try:
            return bytes.fromhex(cleaned)
        except ValueError:
            pass

    key_path = Path(key_arg)
    if key_path.is_file():
        raw = key_path.read_bytes()
        try:
            text = raw.decode("utf-8").strip()
            if len(text) == 64:
                return bytes.fromhex(text)
        except UnicodeDecodeError:
            pass
        if len(raw) == 32:
            return raw

    raise ValueError(f"无效的{label}：请提供 64 位 Hex 字符串或包含该密钥的文件路径。")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="全谱系 12 档动态负载自适应广义 n-EMD / 正交多进制 / 钻石编码 + 元数据无痕透传 + X25519 Elligator 2 图像隐写工具 (v3.3.1)"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # 1. 子命令：pairgen（生成公私钥配对加固混淆脚本）
    p_pair = subparsers.add_parser(
        "pairgen", help="生成一对唯一配对且经密钥分片、AST 控制流平坦化与字节码加密封装的独立嵌入/提取脚本"
    )
    p_pair.add_argument(
        "-d", "--output-dir",
        type=Path,
        default=Path.cwd(),
        help="配对脚本输出目录（默认：当前工作目录）",
    )
    p_pair.add_argument(
        "--prefix",
        default="emd",
        help="生成脚本文件名前缀（默认：emd -> emd_embed_<id>.py / emd_extract_<id>.py）",
    )
    p_pair.add_argument(
        "--no-obfuscate",
        action="store_true",
        help="禁用 AST 控制流平坦化与字节码加密壳，输出可读源码（便于安全审计与跨大版本调试）",
    )

    # 2. 子命令：keygen（生成独立 X25519 公私钥）
    p_key = subparsers.add_parser(
        "keygen", help="生成一组 X25519 非对称公私钥（用于主脚本 --pub-key / --priv-key 模式）"
    )
    p_key.add_argument(
        "-o", "--output-prefix",
        help="将公钥保存至 <prefix>.pub、私钥保存至 <prefix>.key（不指定则直接打印到终端）",
    )

    # 3. 子命令：embed（直接嵌入：支持全谱系 11 档自动切换 + 显式应急档 + 无痕元数据克隆）
    p_embed = subparsers.add_parser("embed", help="将文本或文件自适应选择最优调制档位无痕隐写到图片中")
    p_embed.add_argument("-c", "--cover", required=True, help="输入载体图片路径（支持 PNG/JPG/BMP/WebP/16-bit PNG 等）")
    p_embed.add_argument("-o", "--output", required=True, help="输出隐写图片路径（必须为 .png）")
    auth_emb = p_embed.add_mutually_exclusive_group(required=True)
    auth_emb.add_argument("-p", "--password", help="对称加密与定位口令")
    auth_emb.add_argument("--pub-key", help="接收方 X25519 公钥（64位 Hex 字符串或 .pub 文件路径）")
    payload_grp = p_embed.add_mutually_exclusive_group(required=True)
    payload_grp.add_argument("-m", "--message", help="要隐藏的 UTF-8 文本消息")
    payload_grp.add_argument("-f", "--file", help="要隐藏的任意文件路径")
    p_embed.add_argument(
        "--profile",
        choices=PROFILE_CHOICES,
        default="auto",
        help="调制档位：auto（默认在 emd64..base5 间自动择优最低失真）或手动指定具体档位（含显式应急档 base7）",
    )
    p_embed.add_argument(
        "--compress",
        choices=("auto", "none", "gzip", "bzip2", "xz"),
        default="auto",
        help="隐写前压缩策略：auto（默认自动择优）/ none / gzip / bzip2 / xz",
    )
    p_embed.add_argument(
        "--strip-metadata",
        action="store_true",
        help="主动抹除载体图像的 EXIF / ICC Profile / PNG 辅助块（默认原样无痕透传保留）",
    )

    # 4. 子命令：extract（直接盲提取：全自动识别 12 档隐写档位，兼容 v3.2 历史图像）
    p_extract = subparsers.add_parser("extract", help="从隐写 PNG 图片中全自动识别档位、盲提取并解密数据")
    p_extract.add_argument("-i", "--input", required=True, help="含隐写的 PNG 图片路径")
    auth_ext = p_extract.add_mutually_exclusive_group(required=True)
    auth_ext.add_argument("-p", "--password", help="对称解密与定位口令")
    auth_ext.add_argument("--priv-key", help="接收方 X25519 私钥（64位 Hex 字符串或 .key 文件路径）")
    p_extract.add_argument("-o", "--output", help="将提取结果保存到指定文件（不指定则按 UTF-8 文本打印）")

    # 5. 子命令：capacity（直观对比全谱系 12 档容量、振幅、修改率与元数据块状态）
    p_cap = subparsers.add_parser("capacity", help="查看载体图片在全谱系 12 档下的容量、修改率对比及可透传元数据列表")
    p_cap.add_argument("-c", "--cover", required=True, help="载体图片路径")

    # 6. 子命令：selftest（一键运行全套 6 项密码学、12 档边界、元数据透传与混淆实机自检）
    subparsers.add_parser("selftest", help="运行 Elligator 2、全谱系 12 档边界、元数据透传与加固混淆脚本端到端自检")

    args = parser.parse_args()

    try:
        if args.command == "selftest":
            run_selftest()

        elif args.command == "pairgen":
            embed_path, extract_path, pair_id, fingerprint = generate_pair(
                args.output_dir, prefix=args.prefix, obfuscate=not args.no_obfuscate
            )
            py_ver = f"{sys.version_info.major}.{sys.version_info.minor}"
            print(f"[+] 配对全谱系自适应隐写脚本生成成功！")
            print(f"    配对 ID      : {pair_id}")
            print(f"    公钥指纹     : {fingerprint}")
            print(f"    嵌入脚本(公) : {embed_path}  [支持全谱系 12 档 + 元数据透传，可安全分发]")
            print(f"    提取脚本(私) : {extract_path}  [全自动盲识别档位提取，兼容 v3.2，内含分片私钥请严格保密]")
            print(f"    自适应引擎   : emd64(1.55%) -> emd32 -> emd16 -> emd8 -> emd6 -> emd4 -> emd3 -> emd2 -> base3(±1) -> de13 -> base5(±2) [应急: base7]")
            if not args.no_obfuscate:
                print(
                    f"    代码保护状态 : 4路密钥异或分片 + AST控制流平坦化 + 不透明谓词 + Marshal字节码PBKDF2加密壳 "
                    f"(绑定 Python {py_ver} 字节码；跨 Python 次版本环境可使用 --no-obfuscate)"
                )
            else:
                print("    代码保护状态 : 4路密钥异或分片 + 明文可读源码 (--no-obfuscate，跨任意 Python 3.9+ 版本通用)")

        elif args.command == "keygen":
            priv = x25519.X25519PrivateKey.generate()
            priv_hex = priv.private_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PrivateFormat.Raw,
                encryption_algorithm=serialization.NoEncryption(),
            ).hex()
            pub_bytes = serialize_x25519_public(priv.public_key())
            pub_hex = pub_bytes.hex()
            pair_id = hashlib.sha256(pub_bytes).hexdigest()[:16]

            if args.output_prefix:
                pub_path = Path(f"{args.output_prefix}.pub")
                priv_path = Path(f"{args.output_prefix}.key")
                for p in (pub_path, priv_path):
                    if p.exists():
                        raise FileExistsError(f"拒绝覆盖已存在的密钥文件：{p}")
                pub_path.write_text(pub_hex + "\n", encoding="utf-8")
                priv_path.write_text(priv_hex + "\n", encoding="utf-8")
                if os.name == "posix":
                    priv_path.chmod(0o600)
                print(f"[+] X25519 密钥对已生成（密钥 ID: {pair_id}）：")
                print(f"    公钥文件 : {pub_path}")
                print(f"    私钥文件 : {priv_path}")
            else:
                print(f"[+] X25519 密钥对已生成（密钥 ID: {pair_id}）：")
                print(f"    Public Key  (公钥) : {pub_hex}")
                print(f"    Private Key (私钥) : {priv_hex}")

        elif args.command == "capacity":
            img, meta_bundle = _load_normalized_image(args.cover, preserve_metadata=True)
            channels = len(img.tobytes())
            lsb_cap = max(0, (channels // 8) - 64)
            meta_tags = meta_bundle.summary_tags() if meta_bundle else []
            meta_desc = ", ".join(meta_tags) if meta_tags else "无额外辅助块"
            print(f"[*] 图像尺寸           : {img.size[0]} x {img.size[1]} (源格式: {meta_bundle.source_format if meta_bundle else '?'} -> 隐写模式: {img.mode})")
            print(f"[*] 可透传元数据/色彩块: {meta_desc}")
            print(f"[*] 可用通道总数       : {channels:,}")
            print(f"[*] 传统 1-bit LSB 参考: {lsb_cap:,} 字节 ({lsb_cap / 1024:.2f} KB | 修改率 ~50.00% | 1.000 bpc)")
            print("-" * 108)
            print(f"{'档位':<6} | {'策略':<4} | {'算法模式说明':<34} | {'公钥 ECIES 容量':>14} | {'对称口令容量':>12} | {'振幅':>4} | {'修改率':>8} | {'编码率'}")
            print("-" * 108)
            for prof in PROFILES_ORDERED:
                asym_cap = max_secret_capacity(channels, ASYM_HEADER_CHANNELS, prof)
                sym_cap = max_secret_capacity(channels, SYM_HEADER_CHANNELS, prof)
                policy = "auto" if prof.auto_eligible else "显式"
                print(
                    f"{prof.key:<6} | {policy:<4} | {prof.title:<34} | "
                    f"{asym_cap:>12,} B | {sym_cap:>10,} B | "
                    f"±{prof.max_delta:<3} | ~{prof.expected_mod_rate:>6.2f}% | {prof.bpc:.3f} bpc"
                )
            print("-" * 108)
            print("[*] 提示：默认 --profile auto 将从 emd64 往下自动匹配第一个装得下压缩后载荷的档位（最高至 base5），最大化统计隐蔽性！")

        elif args.command == "embed":
            secret_bytes = (
                args.message.encode("utf-8")
                if args.message is not None
                else Path(args.file).read_bytes()
            )
            preserve_meta = not args.strip_metadata
            if args.pub_key:
                pub_bytes = _parse_key_input(args.pub_key, "X25519 公钥")
                stats = embed_data_ecies(
                    args.cover,
                    args.output,
                    secret_bytes,
                    pub_bytes,
                    args.compress,
                    args.profile,
                    preserve_metadata=preserve_meta,
                )
                mode_desc = "X25519 + Elligator 2 公钥隐匿加密"
            else:
                stats = embed_data(
                    args.cover,
                    args.output,
                    secret_bytes,
                    args.password,
                    args.compress,
                    args.profile,
                    preserve_metadata=preserve_meta,
                )
                mode_desc = "PBKDF2 对称口令加密"

            usage_pct = (stats["stored_bytes"] / stats["max_capacity"] * 100) if stats["max_capacity"] else 100.0
            psnr_str = f"{stats['psnr_db']:.2f} dB" if math.isfinite(stats["psnr_db"]) else "∞ (零修改)"
            meta_str = ", ".join(stats["preserved_metadata"]) if stats["preserved_metadata"] else "无 / 已主动剥离"
            print(f"[+] 自适应隐写成功（{mode_desc}）！已保存至: {args.output}")
            print(f"    自适应档位 : [{stats['profile_key']}] {stats['profile_title']} (最大振幅 ±{stats['max_delta']})")
            print(
                f"    载荷大小   : 原始 {stats['secret_bytes']:,} 字节 -> 压缩后 {stats['stored_bytes']:,} 字节 "
                f"(算法: {stats['codec']}，占该档位容量 {usage_pct:.2f}%)"
            )
            print(
                f"    通道统计   : 使用 {stats['used_channels']:,} / {stats['total_channels']:,} 个通道，"
                f"实际仅修改 {stats['modified_channels']:,} 个通道"
            )
            print(
                f"    隐蔽性指标 : 载荷区修改率 {stats['body_mod_rate']:.2f}% (理论期望 ~{stats['expected_mod_rate']:.2f}%) | "
                f"全图总通道修改率 {stats['overall_img_mod_rate']:.4f}% | 图像质量 PSNR: {psnr_str}"
            )
            print(f"    元数据状态 : 已透传保留块 [{meta_str}]")

        elif args.command == "extract":
            if args.priv_key:
                priv_bytes = _parse_key_input(args.priv_key, "X25519 私钥")
                recovered, prof = extract_data_ecies(args.input, priv_bytes, None)
            else:
                recovered, prof = extract_data(args.input, args.password)

            if args.output:
                Path(args.output).write_bytes(recovered)
                print(
                    f"[+] 盲提取成功（自动识别档位: [{prof.key}] {prof.title}）！"
                    f"已还原 {len(recovered):,} 字节至文件: {args.output}"
                )
            else:
                try:
                    print(
                        f"[+] 盲提取成功（自动识别档位: [{prof.key}] {prof.title}），隐藏文本：\n"
                        + recovered.decode("utf-8")
                    )
                except UnicodeDecodeError:
                    print(
                        f"[!] 盲提取成功（共 {len(recovered):,} 字节，档位: {prof.key}），"
                        f"但内容为二进制数据而非文本，请使用 -o 参数保存到文件。"
                    )

    except Exception as exc:
        print(f"[-] 错误: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()