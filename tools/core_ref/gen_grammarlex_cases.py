import random
import sys

count = int(sys.argv[1])
rng = random.Random(int(sys.argv[2]))
pieces = [
    "int", "char", "foo_bar", "_x1", "struct", "A9", "0", "12", "-7", "0x1f", "0X1", "0x", "1x2", "12ab", "-", "--3",
    "*", ",", "(", ")", "[", "]", "{", "}", ";", "=", ":", "::", ":::", "...", "..", ".", "/", "/* c */", "/* a * b */",
    "/**/", "// line\n", "//", "\"str\"", "\"a b\"", "\"", "'a'", "'\\n'", "'\\0'", "'\\q'", "'ab'", "'", "'\\'",
    " ", "  ", "\t", "\n", "\r", "\x0b", "\x0c", "$", "@", "#", "\x01", "\x7f", "\x80", "\xff", "~", "!",
]


def escape(text):
    result = []
    for char in text:
        code = ord(char)
        if code < 0x21 and char != ' ' or code >= 0x7f or char == '%':
            result.append("%%%02x" % code)
        else:
            result.append(char)
    return "".join(result)


for _ in range(count):
    maxbuf = rng.choice([4, 8, 16, 64, 4096, 4096, 4096])
    parts = []
    for _ in range(rng.randrange(1, 25)):
        parts.append(rng.choice(pieces))
        if rng.random() < 0.5:
            parts.append(rng.choice([" ", "\n", "", "\t"]))
    print("%d %s" % (maxbuf, escape("".join(parts))))
