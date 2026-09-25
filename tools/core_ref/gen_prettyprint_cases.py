import random
import sys

count = int(sys.argv[1])
seed = int(sys.argv[2])
rng = random.Random(seed)
letters = "abcdefghijklmnopqrstuvwxyz_0123456789<>&\"'"


def word():
    size = rng.choice([1, 1, 2, 3, 4, 5, 6, 8, 10, 14, 25])
    text = "".join(rng.choice(letters) for _ in range(size))
    if rng.random() < 0.1:
        text += "\\s" + "".join(rng.choice(letters) for _ in range(3))
    return text


def leaf(lines):
    choice = rng.random()
    color = rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 9, 10])
    if choice < 0.35:
        lines.append("P %d %s" % (color, word()))
    elif choice < 0.5:
        lines.append("V %d %s" % (color, word()))
    elif choice < 0.55:
        lines.append("T %d %s" % (color, word()))
    elif choice < 0.58:
        lines.append("K %d %d %s" % (color, rng.randrange(0, 1 << 20), word()))
    elif choice < 0.8:
        lines.append("S %d %d" % (rng.choice([0, 1, 1, 1, 2, 3, 12]), rng.choice([0, 0, 2, 5, 10])))
    elif choice < 0.9:
        lines.append("L")
    else:
        lines.append("LI %d" % rng.randrange(0, 15))


def block(lines, depth):
    for _ in range(rng.randrange(1, 8)):
        choice = rng.random()
        if depth > 4 or choice < 0.55:
            leaf(lines)
            continue
        kind = rng.choice(["paren", "group", "indent", "comment", "statement", "proto", "brace", "rtype"] * 4 + ["empties"])
        if kind == "paren":
            lines.append("OP " + rng.choice(["(", "[", "{"]))
            block(lines, depth + 1)
            lines.append("CP " + rng.choice([")", "]", "}"]))
        elif kind == "group":
            lines.append("OG")
            block(lines, depth + 1)
            lines.append("CG")
        elif kind == "indent":
            lines.append("SI")
            block(lines, depth + 1)
            lines.append("EI")
        elif kind == "comment":
            lines.append("SC")
            for _ in range(rng.randrange(1, 12)):
                lines.append("P 1 %s" % word())
                lines.append("S 1 0")
            lines.append("EC")
        elif kind == "statement":
            lines.append("BS")
            block(lines, depth + 1)
            lines.append("ES")
        elif kind == "rtype":
            lines.append("BR")
            block(lines, depth + 1)
            lines.append("ER")
        elif kind == "proto":
            lines.append("BP")
            block(lines, depth + 1)
            lines.append("EP")
        elif kind == "brace":
            lines.append("OBI %d {" % rng.randrange(0, 3))
            block(lines, depth + 1)
            lines.append("CBI }")
            if rng.random() < 0.3:
                lines.append("OB %d {" % rng.randrange(0, 3))
        else:
            for _ in range(rng.randrange(40, 400)):
                lines.append(rng.choice(["OG", "SI"]))
                lines.append({"OG": "CG", "SI": "EI"}[lines[-1]])


for _ in range(count):
    maxline = rng.choice([20, 21, 25, 30, 40, 50, 60, 80, 100])
    markup = 1 if rng.random() < 0.2 else 0
    packed = rng.randrange(0, 2)
    lines = ["C %d %d %d" % (maxline, markup, packed)]
    if rng.random() < 0.3:
        lines.append("FILL " + rng.choice(["//\\s", "\\s\\s\\s", "#"]))
    if rng.random() < 0.2:
        lines.append("INC %d" % rng.randrange(0, 6))
    lines.append("BD")
    block(lines, 0)
    lines.append("ED")
    lines.append("F")
    print("\n".join(lines))
