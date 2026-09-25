import random
import sys

count = int(sys.argv[1])
rng = random.Random(int(sys.argv[2]))
base_types = ["int4", "uint4", "int8", "char", "bool", "float4", "float8", "int2", "uint1", "uint8", "int1", "uint2"]
field_names = ["a", "b", "count", "value", "next_field", "x_1", "longer_field_name_for_wrapping", "y"]


def struct_def(name, known):
    fields = []
    for index in range(rng.randrange(1, 7)):
        choice = rng.random()
        if choice < 0.7 or not known:
            tp = rng.choice(base_types)
        else:
            tp = rng.choice(known)
        decl = "%s %s%d" % (tp, rng.choice(field_names), index)
        if rng.random() < 0.03:
            decl = "%s %s%d[%d]" % (tp, rng.choice(field_names), index, rng.choice([2, 4, 10, 16]))
        fields.append(decl + ";")
    return "struct %s { %s };" % (name, " ".join(fields))


def enum_def(name):
    items = []
    value = 0
    for index in range(rng.randrange(1, 8)):
        item = "%s_%s_%d" % (name.upper(), rng.choice(["RED", "GREEN", "MODE", "FLAG", "VERY_LONG_ENUMERATION_NAME"]), index)
        if rng.random() < 0.5:
            value += rng.choice([2, 7, 10, 16, 100, 255, 0x1000, 0xffff, 1024, 99, 0x100000])
            item += " = %d" % value
        else:
            value += 1
        items.append(item)
    return "enum %s { %s };" % (name, ", ".join(items))


lines = []
for _ in range(count):
    defs = []
    known = []
    for index in range(rng.randrange(1, 6)):
        if rng.random() < 0.6:
            name = "st%d" % index
            defs.append(struct_def(name, known))
            known.append(name)
        else:
            name = "en%d" % index
            defs.append(enum_def(name))
            if rng.random() < 0.3:
                known.append(name)
    markup = 1 if rng.random() < 0.3 else 0
    width = rng.choice([20, 30, 40, 60, 80, 100, 100, 120])
    indent = rng.choice([2, 2, 4, 1, 0])
    language = "java" if rng.random() < 0.2 else "c"
    comments = rng.choice(["c", "cplusplus"])
    integers = rng.choice(["best", "best", "hex", "dec"])
    lines.append("%d %d %d %s %s %s %s" % (markup, width, indent, language, comments, integers, "|".join(defs)))
print("\n".join(lines))
