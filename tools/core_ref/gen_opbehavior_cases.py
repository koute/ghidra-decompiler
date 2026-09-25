import random
import sys

INTERESTING = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 128, 0x7f, 0x80, 0xff, 0x100, 0x7fff,
               0x8000, 0xffff, 0x10000, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff,
               0x8000000000000000, 0xfffffffffffffffe, 0xffffffffffffffff, 0x3f800000, 0x40490fdb,
               0x7f800000, 0xff800000, 0x7fc00000, 0x3ff0000000000000, 0x400921fb54442d18,
               0x7ff0000000000000, 0xfff8000000000000, 0xc1e0000000000000, 0x43e0000000000000]
SIZES = [1, 2, 4, 8]
ODD_SIZES = [0, 3, 5, 6, 7, 9, 10, 12, 16, 32, -1]


def value(rng):
    choice = rng.random()
    if choice < 0.45:
        return rng.choice(INTERESTING)
    if choice < 0.6:
        return rng.randint(0, 0x100)
    if choice < 0.85:
        return rng.getrandbits(rng.choice([8, 16, 32, 64]))
    return (rng.choice(INTERESTING) + rng.randint(-3, 3)) & 0xffffffffffffffff


def size(rng):
    if rng.random() < 0.9:
        return rng.choice(SIZES)
    return rng.choice(ODD_SIZES)


def main():
    count = int(sys.argv[1])
    rng = random.Random(int(sys.argv[2]))
    for opc in range(75):
        print("%d m 0 0 0 0 0 0" % opc)
    modes = ["u", "b", "t", "ru", "rb"]
    unary = {1, 17, 18, 24, 25, 37, 46, 51, 52, 53, 54, 55, 56, 57, 58, 59, 72, 73}
    evaluable = [opc for opc in range(1, 74) if opc not in (2, 3, 4, 5, 6, 7, 8, 9, 10, 45, 60, 61, 64, 67, 68, 69, 70, 71)]
    for _ in range(count):
        if rng.random() < 0.1:
            opc = rng.randint(0, 73)
        else:
            opc = rng.choice(evaluable)
        if rng.random() < 0.1:
            mode = rng.choice(modes)
        elif opc in unary:
            mode = "u" if rng.random() < 0.8 else "ru"
        else:
            mode = "b" if rng.random() < 0.75 else "rb"
        sizein = size(rng)
        sizeout = size(rng) if rng.random() < 0.5 else sizein
        if mode == "b" and opc in (29, 30, 31) and rng.random() < 0.5:
            in2 = rng.randint(0, 140)
        elif mode == "rb" and rng.random() < 0.5:
            in2 = rng.randint(0, 70)
        elif mode == "b" and opc == 63:
            in2 = rng.randint(0, 12)
        else:
            in2 = value(rng)
        print("%d %s %d %d %d %x %x %x" % (opc, mode, sizeout, sizein, rng.randint(0, 1), value(rng), in2,
                                           value(rng)))


main()
