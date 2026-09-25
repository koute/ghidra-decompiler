import random
import sys

count = int(sys.argv[1])
rng = random.Random(int(sys.argv[2]))
base_types = ["int4", "uint4", "int8", "char", "bool", "float4", "float8", "void", "int2", "uint1", "int4", "char",
              "uint8", "code", "int4", "uint2", "int1", "float4"]
names = ["a", "b", "x", "foo", "bar_1", "ns::inner", "qq", "a", "b"]
quals = ["const", "volatile", "restrict"]
storage = ["typedef", "extern", "static", "inline", "__stdcall", "__stdcall", "__cdecl"]
struct_names = []
enum_names = []


def base():
    choice = rng.random()
    if choice < 0.65 or not struct_names:
        return rng.choice(base_types)
    if choice < 0.8:
        return "struct " + rng.choice(struct_names)
    if choice < 0.9 and enum_names:
        return "enum " + rng.choice(enum_names)
    if choice < 0.95:
        return "union " + rng.choice(struct_names)
    return rng.choice(struct_names)


def specifiers():
    parts = []
    for _ in range(rng.choice([0, 0, 0, 0, 0, 1, 1, 2])):
        parts.append(rng.choice(quals + storage))
    parts.insert(rng.randrange(0, len(parts) + 1), base())
    if rng.random() < 0.02:
        parts.append(base())
    return " ".join(parts)


def declarator(depth, named=True):
    text = rng.choice(names) if named else ""
    if rng.random() < 0.4:
        stars = "".join(rng.choice(["*", "*", "* const "]) for _ in range(rng.randrange(1, 3)))
        text = stars + text
    for _ in range(rng.choice([0, 0, 1, 1, 2])):
        choice = rng.random()
        if choice < 0.45:
            text = text + "[" + rng.choice(["4", "10", "0x10", "0", "-1", "const 3"]) + "]"
        elif choice < 0.8 and depth < 2:
            text = text + "(" + params(depth + 1) + ")"
        elif named and text:
            text = "(" + text + ")"
    return text


def params(depth):
    if rng.random() < 0.15:
        return "void"
    items = []
    for _ in range(rng.choice([0, 1, 1, 2, 3])):
        items.append(specifiers() + " " + declarator(depth, rng.random() < 0.7))
    if rng.random() < 0.2 or (not items and rng.random() < 0.8):
        items.append("...")
    if items == ["..."] and rng.random() < 0.8:
        items = [specifiers(), "..."]
    return ", ".join(items)


def struct_def():
    name = "s%d" % rng.randrange(0, 6)
    fields = []
    for _ in range(rng.randrange(1, 5)):
        field = specifiers() + " " + declarator(1)
        if rng.random() < 0.15:
            field += " : %d" % rng.randrange(1, 9)
        fields.append(field + ";")
    kind = rng.choice(["struct", "struct", "union"])
    text = "%s %s { %s }" % (kind, name, " ".join(fields))
    struct_names.append(name)
    return text


def enum_def():
    name = "e%d" % rng.randrange(0, 4)
    items = []
    for index in range(rng.randrange(1, 5)):
        item = "V%d_%d" % (rng.randrange(0, 3), index)
        if rng.random() < 0.4:
            item += " = %s" % rng.choice(["1", "0x20", "-3", "'a'", "7"])
        items.append(item)
    enum_names.append(name)
    return "enum %s { %s%s }" % (name, ", ".join(items), rng.choice(["", ","]))


def mutate(text):
    if rng.random() < 0.9:
        return text
    choice = rng.random()
    pos = rng.randrange(0, len(text) + 1)
    if choice < 0.4:
        return text[:pos] + rng.choice([";", ",", "(", ")", "*", "[", "]", "{", "}", "::", "\"s\"", "$", "\n"]) + text[pos:]
    if choice < 0.7:
        return text[:pos] + text[pos + 1:]
    return text + rng.choice([" x", ";", " extra", " /* c */", " // tail"])


lines = []
for _ in range(count):
    choice = rng.random()
    if choice < 0.15:
        lines.append("C " + mutate(struct_def() + ";"))
    elif choice < 0.22:
        lines.append("C " + mutate(enum_def() + ";"))
    elif choice < 0.3:
        lines.append("C " + mutate("typedef " + specifiers() + " " + declarator(0) + ";"))
    elif choice < 0.35:
        lines.append("C " + mutate("extern " + specifiers() + " " + declarator(0) + "(" + params(1) + ");"))
    elif choice < 0.65:
        lines.append("T " + mutate(specifiers() + " " + declarator(0, rng.random() < 0.8)))
    else:
        lines.append("P " + mutate(specifiers() + " " + declarator(0) + "(" + params(1) + ");"))
print("\n".join(line.replace("\n", " ") if rng.random() < 0.5 else line.replace("\n", "\\n") for line in lines))
