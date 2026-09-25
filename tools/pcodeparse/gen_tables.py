import re
import subprocess
import sys

source, target = sys.argv[1], sys.argv[2]
text = open(source).read()
names = ["yytranslate", "yypact", "yydefact", "yypgoto", "yydefgoto", "yytable", "yycheck", "yyr1", "yyr2"]
constants = ["YYFINAL", "YYLAST", "YYNTOKENS", "YYPACT_NINF", "YYTABLE_NINF", "YYMAXUTOK"]
lines = []
for name in constants:
    match = re.search(r"#define %s\s+\(?(-?\d+)\)?" % name, text)
    lines.append("pub const %s: i32 = %d;" % (name, int(match.group(1))))
lines.append("")
for name in names:
    match = re.search(r"static const \w+ %s\[\] =\s*\{([^}]*)\}" % name, text)
    values = [int(value) for value in re.findall(r"-?\d+", match.group(1))]
    lines.append("pub static %s: [i16; %d] = [" % (name.upper(), len(values)))
    for start in range(0, len(values), 16):
        lines.append("    " + ", ".join(str(value) for value in values[start:start + 16]) + ",")
    lines.append("];")
    lines.append("")
with open(target, "w") as handle:
    handle.write("\n".join(lines).rstrip() + "\n")
subprocess.run(["rustfmt", "--edition", "2024", target], check=True)
