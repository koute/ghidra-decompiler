import random
import sys

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
lines = []
values = [0, 1, 9, 10, 11, 99, 100, 101, 999, 1000, 1001, 0xff, 0x100, 0xfff, 0x1000, 0xffffffffffffffff]
for digit_count in range(1, 20):
    for digit in (0, 9):
        for lead in range(1, 30):
            values.append(int(str(lead) + str(digit) * digit_count))
for nibble_count in range(1, 16):
    for nibble in (0, 0xf):
        for lead in range(1, 20):
            values.append((lead << (4 * nibble_count)) | (nibble * ((1 << (4 * nibble_count)) - 1) // 0xf))
for _ in range(2000):
    values.append(rng.getrandbits(rng.choice([4, 8, 12, 16, 24, 32, 48, 64])))
for value in values:
    value &= 0xffffffffffffffff
    lines.append("base %x" % value)
for _ in range(500):
    lines.append("bin %x" % rng.getrandbits(rng.choice([1, 3, 8, 9, 16, 17, 31, 32, 33, 63, 64])))
lines.append("escape 0 200000")
lines.append("escape -100 0")
for value in list(range(-300, 300)) + [rng.randrange(-(1 << 31), 1 << 31) for _ in range(300)]:
    lines.append("hexesc %d" % value)
escape_points = list(range(-5, 0x20)) + [0x22, 0x27, 0x5c, 0x7f, 0x80, 0x9f, 0xa0, 0x61c, 0x1680, 0x180b, 0x180e, 0x2000,
                                           0x200f, 0x2028, 0x202f, 0x205f, 0x2060, 0x2066, 0x206f, 0x3000, 0xd7fc, 0xd800,
                                           0xdfff, 0xe000, 0xf8ff, 0xfe00, 0xfe0f, 0xfeff, 0xfff0, 0xfffb, 0xfffe, 0xffff,
                                           0x2fa20, 0x10ffff, 0x110000, 0x7fffffff, -0x80000000]
for value in escape_points:
    lines.append("uc %d" % value)
    lines.append("uj %d" % value)
print("\n".join(lines))
