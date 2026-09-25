import random
import struct
import sys

SPACES = list(range(1, 14))
ADDR_SPACES = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
INTERESTING = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0xfff, 0x1000, 0xffff, 0x10000, 0x7fffffff, 0x80000000,
               0xffffffff, 0x100000000, 0xffffffffffff, 0x1000000000000, 0x7fffffffffffffff, 0x8000000000000000,
               0xfffffffffffffffe, 0xffffffffffffffff, 0x12345678, 0xdeadbeefcafe]


def hexstr(text):
    return text.encode("latin-1").hex() if text else "-"


def value(rng):
    choice = rng.random()
    if choice < 0.4:
        return rng.choice(INTERESTING)
    if choice < 0.6:
        return rng.randint(0, 0x200)
    if choice < 0.8:
        return rng.getrandbits(rng.choice([8, 16, 32, 48, 64]))
    return rng.choice(INTERESTING) + rng.randint(-3, 3) & 0xffffffffffffffff


def addr(rng):
    return "%d %x" % (rng.choice(ADDR_SPACES), value(rng))


def small_addr(rng, spaces=(2, 3, 5)):
    return "%d %x" % (rng.choice(spaces), rng.randint(0, 0x40))


def size(rng):
    return rng.choice([1, 2, 3, 4, 8, 16, 0, -1, 5, 7])


def read_text(rng):
    pieces = [rng.choice(["eax", "ax", "ebx", "rdx", "sp", "hi", "hilo", "bogus", "0x10", "16", "010", "0x", "-4", "0xffffffffffffffffff",
                          "  7", "abc", ""]),
              rng.choice(["", "", ":4", ":2", "+3", ":0x8+0x10", ":", "+", ":4+", "+-1", ":junk", "zz", ":8+2"])]
    text = "".join(pieces)
    return text


def join_text(rng):
    parts = []
    for _ in range(rng.randint(1, 3)):
        parts.append(rng.choice(["eax", "ebx", "hi", "lo", "r0x10:4", "r0x20:2", "%0x4:4", "b0x100:4", "q0x0", "rbogus", "r", "u0x80:8"]))
    return ",".join(parts)


def float_bits(rng, size):
    choice = rng.random()
    if size == 4:
        if choice < 0.5:
            return rng.choice([0, 0x80000000, 0x3f800000, 0xbf800000, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000,
                               0x7f800001, 0x00000001, 0x80000001, 0x007fffff, 0x00800000, 0x7f7fffff, 0xff7fffff,
                               0x3eaaaaab, 0x34000001, 0x4b000000, 0x4effffff, 0x4f000000, 0xcf000000, 0x5f000000,
                               0x3f000000, 0x3fc00000, 0x40200000, 0xbf000000, 0xbfc00000])
        return rng.getrandbits(32)
    if choice < 0.5:
        return rng.choice([0, 0x8000000000000000, 0x3ff0000000000000, 0x7ff0000000000000, 0xfff0000000000000,
                           0x7ff8000000000000, 0xfff8000000000000, 0x0000000000000001, 0x000fffffffffffff,
                           0x0010000000000000, 0x7fefffffffffffff, 0x3fc5555555555555, 0x3fb999999999999a,
                           0x43e0000000000000, 0xc3e0000000000000, 0x41dfffffffc00000, 0x3fe0000000000000,
                           0x3ff8000000000000, 0x4004000000000000, 0x47efffffe0000000, 0x47efffffffffffff,
                           0x36a0000000000000, 0x3690000000000000, 0x3810000000000000, 0x380fffffffffffff])
    return rng.getrandbits(64)


def host_double(rng):
    choice = rng.random()
    if choice < 0.3:
        return float_bits(rng, 8)
    if choice < 0.6:
        return struct.unpack("<Q", struct.pack("<d", float(struct.unpack("<f", struct.pack("<I", float_bits(rng, 4)))[0])))[0]
    values = [0.1, 1.0 / 3, 2.5, 123456.789, 1e-300, 1e300, -0.0, 5e-324, 3.4028235e38, 1.1754943508222875e-38,
              1.401298464324817e-45, 7.0064923216240854e-46, 0.5, 1e22, 16777217.0, 9007199254740993.0]
    value = rng.choice(values) * rng.choice([1, -1])
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def istream_text(rng):
    return rng.choice(["0", "10", "-10", "0x1f", "0X1F", "017", "08", "0x", "+5", "- 5", "  42", "\t-0x10", "",
                       "   ", "abc", "1e5", "9999999999999999999999", "18446744073709551615", "18446744073709551616",
                       "-9223372036854775808", "-9223372036854775809", "9223372036854775807", "4294967295",
                       "4294967296", "-1", "-2147483648", "-2147483649", "2147483648", "00x10", "0xg", "1.5",
                       "0x8000000000000000", "-0x8000000000000000", "07777777777777777777777", "fff", "0xFfFf",
                       "1 2", "+", "-", "0777", "0000", "0x0", "12abc"])


SPEC_NAMES = ["align", "bigendian", "name", "size", "space", "val", "value", "offset", "piece", "format", "id", "XMLcontent", "storage", "code"]


def mcodec(rng):
    specs = []
    for _ in range(rng.randint(0, 5)):
        kind = rng.choice("SUBTPOI")
        name = rng.choice(SPEC_NAMES[:11] if rng.random() < 0.95 else SPEC_NAMES)
        if kind == "S":
            value = "%x" % (value_any(rng))
        elif kind == "U":
            value = "%x" % (value_any(rng))
        elif kind == "B":
            value = rng.choice(["0", "1"])
        elif kind == "T":
            value = rng.choice(["", "hello", "ram", "INT_ADD", "0x10", "-7", "true", "abc def", "piece", "12x"])
        elif kind == "P":
            value = str(rng.randint(0, 13))
        elif kind == "O":
            value = str(rng.randint(1, 73))
        else:
            name = "piece"
            value = str(rng.randint(0, 9)) + rng.choice(["ram:0x0:4", "x", ""])
        specs.append("%s:%s=%s" % (kind, name, value))
    reads = "".join(rng.choice("SUBTPOEIX") for _ in range(rng.randint(0, 6)))
    return "mcodec %s %s" % (hexstr(";".join(specs)), hexstr(reads))


def value_any(rng):
    return rng.choice([0, 1, 0x7f, 0x80, 0x3fff, 0x4000, 0x1fffff, 0x200000, 0xfffffff, 0x10000000, 0x7ffffffff,
                       0x800000000, 0x3ffffffffff, 0x40000000000, 0x1ffffffffffff, 0x2000000000000,
                       0xffffffffffffff, 0x100000000000000, 0x7fffffffffffffff, 0x8000000000000000,
                       0xffffffffffffffff, 0xfffffffffffffff0, rng.getrandbits(64)])


RANGE_XML = ['<range space="ram" first="0x10" last="0x20"/>', '<register name="eax"/>', '<range space="ram"/>',
             '<range first="1"/>', '<range space="ram" first="0x30" last="0x20"/>', '<range space="Tiny" first="0" last="0x100"/>',
             '<bogus/>', '<range space="nospace"/>', '<range space="Tiny" first="0x10"/>', '<register name="nothere"/>',
             '<range space="register" first="0x4" last="0x7" name="ebx"/>', '<range name="hilo" space="ram"/>']

RANGELIST_XML = ['<rangelist><range space="ram" first="0x1" last="0x5"/><register name="ebx"/></rangelist>', '<rangelist/>',
                 '<rangelist><range space="ram" first="1" last="5"/><range space="ram" first="1" last="9"/></rangelist>',
                 '<rangelist><range space="bram" first="0x10" last="0x20"/><range space="ram" first="0x30" last="0x40"/><range space="ram" first="0x0" last="0x2"/></rangelist>',
                 '<rangelist><range space="ram" first="5" last="1"/></rangelist>', '<list/>']

PCODE_XML = ['<op code="INT_ADD" size="2"><addr space="register" offset="0" size="4"/><addr space="register" offset="4" size="4"/><addr space="const" offset="1" size="4"/></op>',
             '<op code="STORE" size="2"><void/><addr space="register" offset="0x8" size="8"/><addr space="unique" offset="0x100" size="4"/></op>',
             '<op code="BOGUS" size="0"><void/></op>', '<op code="COPY" size="-1"><void/></op>',
             '<op code="LOAD" size="1"><addr name="eax"/><addr name="rdx"/></op>',
             '<op code="CALL" size="1"><void/><addr space="join" piece1="eax" piece2="ebx"/></op>',
             '<op code="BRANCH" size="1"><void/><addr space="code16" offset="0x11" size="2"/></op>',
             '<op code="UNUSED1" size="0"><void/></op>', '<op size="0"><void/></op>', '<opx code="COPY" size="0"/>',
             '<op code="COPY" size="1"><addr space="data4" offset="0x5" size="4"/><spaceid name="nospace"/></op>']

CTX_SPEC_XML = ['<context_data><context_set space="ram" first="0x10" last="0x20"><set name="mode" val="3"/><set name="big" val="0x1234"/></context_set></context_data>',
                '<context_data><tracked_set space="ram" first="0x0" last="0x5"><set space="register" offset="0x0" size="4" val="0x10"/><set name="ebx" val="7"/></tracked_set></context_data>',
                '<context_data><context_set space="ram" first="0x30" last="0x20"><set name="mode" val="3"/></context_set></context_data>',
                '<context_data><context_set space="ram" first="0x8"><set name="flag" val="1"/></context_set></context_data>',
                '<context_data><bogus space="ram" first="0x8"/></context_data>',
                '<context_data><context_set space="ram" first="0x2" last="0x4"><set name="nothere" val="1"/></context_set></context_data>',
                '<context_data><context_set space="bram" first="0x2" last="0x4"><set name="word2" val="0x1ff"/><set name="top" val="9"/></context_set></context_data>']


def generate(rng, count):
    lines = []
    for index in SPACES:
        lines.append("space %d" % index)
    for code in list(range(0x20, 0x7f)) + [0x80, 0xff]:
        lines.append("shortcut %x" % code)
    for index in [-1] + SPACES:
        lines.append("nextspace %d" % index)
    ctx_names = []
    context_ready = False
    tracked_open = False
    while len(lines) < count:
        choice = rng.random()
        if choice < 0.08:
            lines.append("printraw %s" % addr(rng))
        elif choice < 0.11:
            space = rng.choice(ADDR_SPACES)
            lines.append("wrap %d %x" % (space, value(rng)))
        elif choice < 0.13:
            lines.append("add %s %x" % (addr(rng), value(rng)))
        elif choice < 0.17:
            lines.append("read %d %s" % (rng.choice(ADDR_SPACES), hexstr(read_text(rng))))
        elif choice < 0.19:
            lines.append("read 13 %s" % hexstr(join_text(rng)))
        elif choice < 0.23:
            lines.append("overlap %s %d %s %d" % (small_addr(rng), rng.randint(-2, 8), small_addr(rng), size(rng)))
        elif choice < 0.27:
            lines.append("justified %s %d %s %d %d" % (small_addr(rng), size(rng), small_addr(rng), size(rng), rng.randint(0, 1)))
        elif choice < 0.28:
            lines.append("validrange %s %x" % (addr(rng), value(rng)))
        elif choice < 0.33:
            count_pieces = rng.choice([0, 1, 1, 2, 2, 2, 3])
            pieces = " ".join("%s %d" % (small_addr(rng, (2, 3, 5, 8)), rng.choice([1, 2, 4, 8, 0])) for _ in range(count_pieces))
            logical = rng.choice([0, 0, 0, 4, 8, 10])
            lines.append("join %d %s %d" % (count_pieces, pieces, logical) if count_pieces else "join 0 %d" % logical)
        elif choice < 0.35:
            lines.append("joinequiv %x %x" % (rng.choice([0, 0x10, 0x20, 0x30, 0x40, 0x50, 0x5]), rng.randint(0, 0x60)))
        elif choice < 0.37:
            lines.append("renorm 13 %x %d" % (rng.randint(0, 0x60), rng.choice([1, 2, 4, 6, 8, 12, 16])))
        elif choice < 0.40:
            lines.append("cjoin %s %d %s %d" % (small_addr(rng, (2, 3, 5, 8, 4)), rng.choice([1, 2, 4]), small_addr(rng, (2, 3, 5, 8, 4)), rng.choice([1, 2, 4])))
        elif choice < 0.41:
            lines.append("cwrap %d %x %d" % (rng.choice(ADDR_SPACES), rng.choice([0xfffffffffffffffe, 0xfffffffe, 0xfffe, 0xff, 0x10, 0xfffffffffff0]), rng.choice([1, 2, 4, 8, 16])))
        elif choice < 0.42:
            lines.append("cfloat %s %d %d" % (small_addr(rng), rng.choice([4, 8]), rng.choice([4, 8, 10, 16])))
        elif choice < 0.43:
            lines.append("strip %x %d" % (rng.choice([0, 0x10, 0x20, 0x30]), rng.randint(0, 3)))
        elif choice < 0.47:
            space = rng.choice(ADDR_SPACES + [13])
            offset = rng.choice([0, 0x10, 0x20, 0x30]) if space == 13 else value(rng)
            lines.append("encode %d %x %d" % (space, offset, rng.choice([-1, 4, 8])))
        elif choice < 0.50:
            packed = rng.randint(0, 1)
            if packed:
                data = bytes(rng.choice([0x4b, 0xd4, 0xc5, 0x80, 0xcb, 0x50, 0xd0, 0x82, 0x88, 0x51, 0xde, 0x13, 0x8b, 0x00, 0xce]) for _ in range(rng.randint(0, 10)))
                data = rng.choice([b"\x4b\xd4\x51\x82\xd0\x81\x90\xd3\x21\x84\x8b", b"\x4b\xce\x71\x84\x8b", b"\x4b\x8b",
                                   b"\x4b\xd4\x51\x81\x8b", b"\x4b\xd4\x51\xd0\x42\x81\x8b", b"\x4b\xd4\x53\xd0\x42\x81\x8b",
                                   b"\x4b\xd4\x6d\xd0\x42\x81\x8b", b"\x4b\xd4\x51\xd0\x42\x81\xd3\x31\x84\x8b",
                                   b"\x4b\xd4\x51\xd0\x42\x81\xd3\x22\x84\x8b", b"\x4b\xd4\x61\xd0\x42\x81\x8b"])
                lines.append("decode 1 %s" % data.hex())
            else:
                text = rng.choice(['<addr space="ram" offset="0x10" size="4"/>', '<addr space="register" offset="0x8"/>',
                                   '<addr name="eax"/>', '<addr/>', '<addr space="bogus" offset="1"/>',
                                   '<addr space="join" piece1="register:0x0:4" piece2="register:0x4:4"/>',
                                   '<addr space="join" piece1="eax" piece2="ebx"/>', '<addr space="join" piece1="ram:0x10:8" logicalsize="16"/>',
                                   '<addr space="join" piece1="register:0x0" />', '<addr space="join" piece2="ram:0x0:2" piece1="ram:0x4:2"/>',
                                   '<addr space="ram" size="4"/>', '<addr space="code16" offset="0x11" size="2"/>',
                                   '<varnode space="ram" offset="-1" size="0x10"/>', '<addr name="bogus"/>',
                                   '<addr space="join" piece0="ram:0x0:2"/>', '<addr space="join" pieceX="ram:0x0:2"/>'])
                lines.append("decode 0 %s" % hexstr(text))
        elif choice < 0.52:
            text = rng.choice(["0x1000", "ram:0x10", "register:0x4", "bogus:0x10", "code16:0x10", "10", "data4:0xffffff", "ram:zz", ":1"])
            lines.append("parse %s" % hexstr(text))
        elif choice < 0.53 and len(lines) > count * 0.8:
            lines.append("truncate %s %d" % (hexstr(rng.choice(["ram", "rom", "bram", "nothere"])), rng.choice([2, 4, 6])))
        elif choice < 0.54:
            lines.append("nearptr %d %d" % (rng.choice(ADDR_SPACES), rng.choice([2, 4, 8])))
        elif choice < 0.55:
            space = rng.choice([2, 3, 5, 10])
            first = rng.randint(0, 0x100)
            lines.append("nohighptr %d %x %x" % (space, first, first + rng.randint(0, 0x100)))
        elif choice < 0.57:
            lines.append("highptr %s %d" % (small_addr(rng, (2, 3, 5, 10)), rng.choice([1, 4, 8])))
        elif choice < 0.58:
            space = rng.choice(ADDR_SPACES)
            lines.append("lastopen %d %x %x" % (space, rng.randint(0, 0x100), rng.choice([0x200, 0xffffffffffffffff, 0xffffffff, 0xffff, 0xff, 0xffffff])))
        elif choice < 0.64:
            space = rng.choice([2, 3, 5])
            first = rng.randint(0, 0x80)
            last = first + rng.randint(0, 0x20)
            lines.append("rl_%s %d %x %x" % (rng.choice(["insert", "insert", "remove"]), space, first, last))
        elif choice < 0.66:
            lines.append("rl_query %d %x %x" % (rng.choice([2, 3, 5]), rng.randint(0, 0xa0), rng.choice([1, 2, 4, 16, 0x40, 0])))
        elif choice < 0.665:
            lines.append(rng.choice(["rl_print", "rl_encode", "rl_clear"]))
        elif choice < 0.72:
            lines.append("helper %x %d %d" % (value(rng), rng.randint(-2, 12), rng.randint(-2, 12)))
        elif choice < 0.77:
            kind = rng.choice(["u64", "i64", "u32", "i32"])
            base = rng.choice(["auto", "auto", "hex", "dec", "oct"])
            lines.append("istream %s %s %s" % (kind, base, hexstr(istream_text(rng))))
        elif choice < 0.79:
            lines.append("strtoul %s" % hexstr(istream_text(rng)))
        elif choice < 0.82:
            size_value = rng.choice([4, 8])
            lines.append("fhost %d %x" % (size_value, float_bits(rng, size_value)))
        elif choice < 0.85:
            lines.append("fenc %d %x" % (rng.choice([4, 8]), host_double(rng)))
        elif choice < 0.89:
            lines.append("fprint %d %x" % (rng.choice([4, 8]), host_double(rng)))
        elif choice < 0.93:
            size_value = rng.choice([4, 8])
            lines.append("fop %d %x %x" % (size_value, float_bits(rng, size_value), float_bits(rng, size_value)))
        elif choice < 0.945:
            lines.append(mcodec(rng))
        elif choice < 0.95:
            sub = rng.random()
            if sub < 0.1:
                lines.append("nested %d" % rng.randint(0, 16))
            elif sub < 0.3:
                lines.append("rangedecode %s" % hexstr(rng.choice(RANGE_XML)))
            elif sub < 0.45:
                lines.append("rangeprops %s" % hexstr(rng.choice(RANGE_XML)))
            elif sub < 0.55:
                lines.append("rldecode %s" % hexstr(rng.choice(RANGELIST_XML)))
            elif sub < 0.75:
                lines.append("pcodeop %s %s" % (addr(rng), hexstr(rng.choice(PCODE_XML))))
            elif sub < 0.9:
                seq = rng.choice([[(3, 4, 4), (3, 0, 4)], [(3, 0xc, 4), (3, 8, 4)], [(5, 0x100, 4), (5, 0x104, 4)], [(3, 0, 2), (3, 4, 4)],
                                  [(3, 0xc, 4), (3, 8, 4), (3, 4, 4), (3, 0, 4)], [(2, 0x10, 4), (2, 0xc, 4)], [(8, 0x10, 4), (8, 0xc, 4)],
                                  [(3, 0, 4)], [(5, 0x104, 4), (5, 0x100, 4)]])
                lines.append("merge %d %s" % (len(seq), " ".join("%d %x %d" % item for item in seq)))
            else:
                lines.append("resolve %d %x %d" % (rng.choice(ADDR_SPACES), value(rng), rng.choice([1, 2, 4, 8])))
        else:
            if not context_ready:
                for name, sbit, ebit in [("mode", 0, 3), ("flag", 4, 4), ("big", 8, 23), ("word2", 32, 40), ("top", 60, 63)]:
                    lines.append("ctx_register %s %d %d" % (name, sbit, ebit))
                    ctx_names.append(name)
                lines.append("ctx_register bad 30 33")
                context_ready = True
                continue
            sub = rng.random()
            name = rng.choice(ctx_names + ["missing"])
            if sub < 0.15:
                lines.append("ctx_default %s %x" % (name, rng.getrandbits(32)))
            elif sub < 0.35:
                lines.append("ctx_setvar %s %s %x" % (name, small_addr(rng, (2, 5)), rng.getrandbits(32)))
            elif sub < 0.5:
                space1 = rng.choice([2, 5])
                space2 = rng.choice([space1, 5])
                offset1 = rng.randint(0, 0x40)
                offset2 = offset1 + rng.randint(1, 0x10) if space2 == space1 else rng.randint(0, 0x40)
                lines.append("ctx_region %s %d %x %d %x %x" % (name, space1, offset1, space2, offset2, rng.getrandbits(32)))
            elif sub < 0.55:
                lines.append("ctx_changepoint %s %d %x %x" % (small_addr(rng, (2, 5)), rng.randint(0, 1), rng.getrandbits(32), rng.getrandbits(32)))
            elif sub < 0.75:
                lines.append("ctx_get %s %s" % (name, small_addr(rng, (2, 5))))
            elif sub < 0.85:
                first = rng.randint(0, 0x30)
                lines.append("ctx_tracked 2 %x 2 %x" % (first, first + rng.randint(1, 0x10)))
                for _ in range(rng.randint(0, 3)):
                    lines.append("ctx_trackadd %s %d %x" % (small_addr(rng, (3, 5)), rng.choice([1, 2, 4, 8]), rng.getrandbits(64)))
            elif sub < 0.9:
                lines.append("ctx_trackval %s %d %s" % (small_addr(rng, (3, 5)), rng.choice([1, 2, 4]), small_addr(rng, (2,))))
            elif sub < 0.92:
                lines.append("ctx_encode")
            elif sub < 0.93:
                lines.append("ctx_roundtrip")
            elif sub < 0.94:
                lines.append("ctx_spec %s" % hexstr(rng.choice(CTX_SPEC_XML)))
            elif sub < 0.97:
                lines.append("cache_get %s" % small_addr(rng, (2, 5)))
            elif sub < 0.98:
                lines.append("cache_set %s %d %x %x" % (small_addr(rng, (2, 5)), rng.randint(0, 1), rng.getrandbits(32), rng.getrandbits(32)))
            elif sub < 0.99:
                first = rng.randint(0, 0x30)
                lines.append("cache_region 2 %x 2 %x %d %x %x" % (first, first + rng.randint(1, 0x10), rng.randint(0, 1), rng.getrandbits(32), rng.getrandbits(32)))
            else:
                lines.append("cache_allow %d" % rng.choice([0, 1, 1]))
    lines.append("rl_print")
    lines.append("rl_encode")
    lines.append("ctx_encode")
    for index in SPACES:
        lines.append("space %d" % index)
    return lines


def main():
    count = int(sys.argv[1])
    seed = int(sys.argv[2])
    rng = random.Random(seed)
    for line in generate(rng, count):
        print(line)


main()
