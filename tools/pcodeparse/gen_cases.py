import os
import random
import re
import subprocess
import sys
import xml.etree.ElementTree as ElementTree

root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
languages_dir = os.path.join(root, "crates", "ghidra-decompiler", "languages")
probe = os.path.join(root, "tools", "core_ref", "pcodeparse_probe")
out_dir = os.path.join(root, "crates", "ghidra-decompiler", "tests", "pcodeparse_data")
fuzz_count = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 17
rng = random.Random(seed)

files = {}
for processor in sorted(os.listdir(languages_dir)):
    for dirpath, _, names in sorted(os.walk(os.path.join(languages_dir, processor))):
        for name in sorted(names):
            files.setdefault(name, os.path.relpath(os.path.join(dirpath, name), languages_dir))


def escape(text):
    out = []
    for byte in text.encode("latin-1"):
        if byte < 0x20 or byte >= 0x7F or byte == 0x5C:
            out.append("\\x%02x" % byte)
        else:
            out.append(chr(byte))
    return "".join(out)


def snippets(spec):
    try:
        tree = ElementTree.parse(os.path.join(languages_dir, spec))
    except ElementTree.ParseError:
        return []
    res = []
    for element in tree.iter():
        if not element.tag.endswith("pcode"):
            continue
        body = element.find("body")
        if body is None or body.text is None:
            continue
        names = [child.get("name") for child in element if child.tag == "input"]
        names += [child.get("name") for child in element if child.tag == "output"]
        res.append((",".join(names) if names else "-", body.text))
    return res


real_cases = []
seen = set()
for name in sorted(files):
    if not name.endswith(".ldefs"):
        continue
    definitions = ElementTree.parse(os.path.join(languages_dir, files[name])).getroot()
    for language in definitions.iter("language"):
        sla = files.get(language.get("slafile"))
        if sla is None:
            continue
        specs = [language.get("processorspec")] + [compiler.get("spec") for compiler in language.iter("compiler")]
        for spec in specs:
            if spec not in files:
                continue
            for operands, body in snippets(files[spec]):
                key = (sla, operands, body)
                if key in seen:
                    continue
                seen.add(key)
                real_cases.append(key)

primary_slas = [files[name] for name in ["x86-64.sla", "x86.sla", "ARM8_le.sla", "ARM8_be.sla", "AARCH64.sla",
                                          "mips32be.sla", "mips64le.sla", "ppc_32_be.sla", "ppc_64_le.sla",
                                          "riscv.lp64d.sla"] if name in files]
fragments = ["local", "goto", "call", "return", "if", "zext", "sext", "carry", "scarry", "sborrow", "borrow",
             "abs", "sqrt", "nan", "trunc", "ceil", "floor", "round", "int2float", "float2float", "newobject",
             "inst_next", "inst_start", "inst_dest", "inst_ref", "inst_next2", "ram", "register", "unique",
             "const", "OTHER", "tmp", "x", "y", "lbl", "a", "b", "c", "RAX", "EAX", "r0", "r1", "sp", "pc", "lr",
             "x0", "w1", "CF", "ZF", "NG", "a0", "t0", "ctr", "CALLOTHER", "segment", "0", "1", "4", "8", "0x10",
             "0xffffffffffffffff", "0x1ffffffffffffffff", "18446744073709551616", "007", "09", "0x", "123",
             "=", ";", ":", ",", "(", ")", "[", "]", "<", ">", "*", "&", "+", "-", "/", "%", "^", "|", "~", "!",
             "==", "!=", "<=", ">=", "<<", ">>", "s>>", "s<", "s<=", "s>", "s>=", "s/", "s%", "f+", "f-", "f*",
             "f/", "f<", "f<=", "f>", "f>=", "f==", "f!=", "&&", "||", "^^", "#", "\n", " ", "@", "$", "\t"]
templates = [
    "x = y + 1;", "local t:4 = x; y = t;", "*[ram]:4 x = y;", "x = *:2 y;", "goto inst_next;",
    "if (x == 0) goto <done>; x = x - 1; <done>", "call [x];", "return [y];", "x[0,8] = y;",
    "t = x:2;", "t = x[4,4];", "t = x(1);", "t = &x;", "t = &:2 y;", "local u; u = zext(x);",
    "tmp:8 = sext(x) * 3;", "goto 0x1000;", "goto 0x1000[ram];", "x = carry(x,y); y = scarry(x,y);",
    "<a> goto <a>;", "<a> <a>", "goto <b>;", "x = newobject(y);", "x = y f+ x;", "a = b s>> 1;",
    "local x = 1;", "x:4 = 5;", "y = inst_ref;", "goto inst_dest;", "x = -y; y = ~x; z = !x;",
    "t = REG[64,8];", "t = REG[4,4];", "t = REG[8,16];", "REG[0,8] = x;", "REG[3,5] = y;", "t = REG:1;",
    "REG = REG + x;", "t:2 = REG(2);", "*[ram]:4 REG = t;", "REG[0,64] = 1;", "t = REG[0,9];",
    "local q = x; *[ram]:2 y = q; *[ram]:4 y = q;", "t = x:2; u:4 = t;", "t = x[0,12];", "REG[60,8] = x;",
]
registers = {"x86-64.sla": ["RAX", "EAX", "AL", "CF"], "x86.sla": ["EAX", "AX", "ESP"],
             "ARM8_le.sla": ["r0", "r1", "sp", "NG"], "ARM8_be.sla": ["r0", "lr"],
             "AARCH64.sla": ["x0", "w1", "sp"], "mips32be.sla": ["a0", "t0", "sp"],
             "mips64le.sla": ["a0", "v0"], "ppc_32_be.sla": ["r3", "ctr", "lr"],
             "ppc_64_le.sla": ["r3", "r4"], "riscv.lp64d.sla": ["a0", "t0", "sp"]}


def random_snippet(sla):
    registers_for = registers.get(os.path.basename(sla), ["x"])
    return random_text().replace("REG", rng.choice(registers_for))


def random_text():
    choice = rng.random()
    if choice < 0.35:
        count = rng.randint(1, 20)
        return " ".join(rng.choice(fragments) for _ in range(count))
    if choice < 0.6:
        text = " ".join(rng.choice(templates) for _ in range(rng.randint(1, 4)))
        return mutate(text)
    if choice < 0.9 and real_cases:
        return mutate(rng.choice(real_cases)[2])
    if choice < 0.95:
        return rng.choice(templates) + chr(rng.randint(0, 255))
    return "".join(chr(rng.randint(1, 127)) for _ in range(rng.randint(1, 30)))


def mutate(text):
    tokens = re.findall(r"\s+|[A-Za-z_.][A-Za-z0-9_.]*|0x[0-9a-fA-F]*|\d+|.", text, re.S)
    for _ in range(rng.randint(0, 3)):
        action = rng.random()
        if not tokens:
            tokens.append(rng.choice(fragments))
            continue
        position = rng.randrange(len(tokens))
        if action < 0.3:
            del tokens[position]
        elif action < 0.6:
            tokens.insert(position, " " + rng.choice(fragments) + " ")
        else:
            tokens[position] = rng.choice(fragments)
    return "".join(tokens)


fuzz_cases = []
for index in range(fuzz_count):
    sla = rng.choice(primary_slas)
    operands = rng.choice(["-", "x", "x,y", "x,y", "x,y", "x,y,z", "a,b,c", "tmp"] * 8 + ["x,x", "inst_dest"])
    fuzz_cases.append((sla, operands, random_snippet(sla)))
for sla in primary_slas[:2]:
    fuzz_cases.append((sla, "-", "x = " + "(" * 12000 + "1" + ")" * 12000 + ";"))
    fuzz_cases.append((sla, "-", "x = " + "(" * 9990 + "1" + ")" * 9990 + ";"))
    fuzz_cases.append((sla, "-", "x = " + "-" * 5000 + "1;"))
    fuzz_cases.append((sla, "-", ""))
    fuzz_cases.append((sla, "-", "x = 1; \x00 y = 2;"))


def case_line(case, base):
    sla, operands, body = case
    return "%s\t%x\t%s\t%s" % (sla, base, operands, escape(body))


def run_probe(lines):
    result = subprocess.run([probe, languages_dir], input="".join(line + "\n" for line in lines).encode("latin-1"),
                            capture_output=True)
    output = result.stdout.decode("latin-1").splitlines()
    return result.returncode, output


lines = []
for case in real_cases:
    lines.append(case_line(case, rng.choice([0x2000, 0x200, 0x10000])))
for case in fuzz_cases:
    lines.append(case_line(case, rng.choice([0x2000, 0x0, 0x10000, 0xfffffff0])))

kept_lines = []
kept_output = []
chunk = 400
for start in range(0, len(lines), chunk):
    part = lines[start:start + chunk]
    status, output = run_probe(part)
    if status == 0 and len(output) == len(part):
        kept_lines.extend(part)
        kept_output.extend(output)
        continue
    for line in part:
        status, output = run_probe([line])
        if status == 0 and len(output) == 1:
            kept_lines.append(line)
            kept_output.append(output[0])
        else:
            sys.stderr.write("dropping crashing case: %s\n" % line[:120])

os.makedirs(out_dir, exist_ok=True)
with open(os.path.join(out_dir, "cases.txt"), "w", encoding="latin-1") as handle:
    handle.write("".join(line + "\n" for line in kept_lines))
with open(os.path.join(out_dir, "expected.txt"), "w", encoding="latin-1") as handle:
    handle.write("".join(line + "\n" for line in kept_output))
counts = {}
for line in kept_output:
    counts[line.split("\t")[0]] = counts.get(line.split("\t")[0], 0) + 1
print("real snippets: %d, fuzz: %d, kept: %d, outcomes: %s" % (len(real_cases), len(fuzz_cases), len(kept_lines), counts))
