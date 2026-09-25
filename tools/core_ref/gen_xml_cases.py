import random
import sys

NAME_START = "abcXYZ_:"
NAME_CHARS = NAME_START + "019.-"
TOKENS = ['<', '>', '&', ';', '"', "'", '=', ' ', '\n', '\t', '\r', '/', '!', '?', '-', '[', ']', 'x', '#',
          'a', ':', '\x00', '\xff', 'é', '<!--', '-->', '<![CDATA[', ']]>', '<?', '?>', '&#', '&amp;',
          '&#x41;', '&#65;', 'DOCTYPE', '<?xml version="1.0"?>', '<!DOCTYPE', '&lt;', '&bogus;', '&#x;', '&#;',
          '<a>', '</a>', '<b/>', ' c="d"', '\x01', '\x1f']


def name(rng):
    text = rng.choice(NAME_START)
    for _ in range(rng.randint(0, 4)):
        text += rng.choice(NAME_CHARS)
    return text


def attr_value(rng, quote):
    parts = []
    for _ in range(rng.randint(0, 4)):
        choice = rng.random()
        if choice < 0.5:
            parts.append(rng.choice(["x", "1", "hello world", "0x10", "-5", " ", "é", "\t", "a'b" if quote == '"' else 'a"b']))
        elif choice < 0.8:
            parts.append(rng.choice(["&lt;", "&gt;", "&amp;", "&quot;", "&apos;", "&#65;", "&#x4a;", "&#300;", "&#xc2;&#xa3;", "&zz;"]))
        else:
            parts.append(rng.choice([">", "=", "/"]))
    return quote + "".join(parts) + quote


def element(rng, depth):
    tag = name(rng)
    text = "<" + tag
    for _ in range(rng.randint(0, 3)):
        quote = rng.choice(['"', "'"])
        eq = rng.choice(["=", " =", "= ", " = ", "\n=\t"])
        text += rng.choice([" ", "\n", "  ", "\t"]) + name(rng) + eq + attr_value(rng, quote)
    text += rng.choice(["", "", " ", "\n"])
    if depth > 3 or rng.random() < 0.3:
        return text + "/>"
    text += ">"
    for _ in range(rng.randint(0, 4)):
        choice = rng.random()
        if choice < 0.35:
            text += element(rng, depth + 1)
        elif choice < 0.6:
            text += rng.choice(["hi", " ", "\n  ", "text & more".replace("&", "&amp;"), "été", "a]b", "]]", "x > y"])
        elif choice < 0.7:
            text += rng.choice(["&lt;", "&#32;", "&#x20;", "&#65;", "&unknown;", "&#xc2;&#xa3;"])
        elif choice < 0.8:
            text += "<![CDATA[" + rng.choice(["", " ", "a<b", "x]y", "é", "]]"]) + "]]>"
        elif choice < 0.9:
            text += "<!--" + rng.choice(["", " c ", "-x", "é", "a-b"]) + "-->"
        else:
            text += rng.choice(["<?pi x?>", "\t", "\r\n", "\t", "\r\n", "\t", "\r\n", "\t"])
    closing = tag if rng.random() < 0.9 else name(rng)
    return text + "</" + closing + rng.choice(["", " ", "\n"]) + ">"


def document(rng):
    prolog = ""
    choice = rng.random()
    if choice < 0.3:
        prolog = rng.choice(['<?xml version="1.0"?>', "<?xml version='1.0' encoding='UTF-8'?>",
                             '<?xml version = "1.0" encoding="x" ?>', '<?xml  version="1.0"   ?>',
                             '<?xml version="1&amp;"?>', '<?xmlversion="1.0"?>', '<?xml?>'])
    for _ in range(rng.randint(0, 2)):
        prolog += rng.choice(["\n", " ", "<!-- pro -->", "<!DOCTYPE x>", "<?pi?>", "\t\r\n", "\n", "<!---->"])
    epilog = rng.choice(["", "", "", "", "\n", "  \n ", "\n\n", "", "<!-- e -->", "<?e?>", "x"])
    return prolog + element(rng, 0) + epilog


def mutate(rng, text):
    for _ in range(rng.randint(1, 3)):
        pos = rng.randint(0, len(text))
        choice = rng.random()
        if choice < 0.4 and len(text) > 0:
            end = min(len(text), pos + rng.randint(1, 3))
            text = text[:pos] + text[end:]
        elif choice < 0.8:
            text = text[:pos] + rng.choice(TOKENS) + text[pos:]
        else:
            text = text[:pos] + chr(rng.randint(1, 127)) + text[pos + 1:]
    return text


def encode(text):
    data = bytearray()
    for character in text:
        code = ord(character)
        if code == 0xff:
            data.append(0xff)
        else:
            data.extend(character.encode("utf-8"))
    return bytes(data)


def nested(depth, prolog, leaf):
    return prolog + "<a>" * depth + leaf + "</a>" * depth + "\n"


def main():
    count = int(sys.argv[1])
    seed = int(sys.argv[2])
    rng = random.Random(seed)
    cases = []
    depths = list(range(4990, 5003)) if len(sys.argv) < 4 else []
    for depth in depths:
        for prolog in ["", " ", '<?xml version="1.0"?>']:
            for leaf in ["", "<b/>", '<b c="&lt;"/>', "<!-- x -->", "t&amp;", "<![CDATA[x]]>", "<b></b >"]:
                cases.append(encode(nested(depth, prolog, leaf)))
    while len(cases) < count:
        text = document(rng)
        if rng.random() < 0.4:
            text = mutate(rng, text)
        cases.append(encode(text))
    for case in cases:
        print(case.hex())


main()
