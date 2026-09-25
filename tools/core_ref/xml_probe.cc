#include "xml.hh"
#include <iostream>
#include <sstream>
#include <string>

using namespace ghidra;

static void dumpString(std::ostream &s, const string &text)
{
  s << text.size() << ':';
  for (size_t index = 0; index < text.size(); ++index) {
    unsigned char byte = (unsigned char)text[index];
    static const char *hexdigits = "0123456789abcdef";
    s << hexdigits[byte >> 4] << hexdigits[byte & 15];
  }
}

static void dumpElement(std::ostream &s, const Element *el)
{
  s << '(';
  dumpString(s, el->getName());
  s << ' ' << el->getNumAttributes();
  for (int index = 0; index < el->getNumAttributes(); ++index) {
    s << ' ';
    dumpString(s, el->getAttributeName(index));
    s << ' ';
    dumpString(s, el->getAttributeValue(index));
  }
  s << ' ';
  dumpString(s, el->getContent());
  const List &children(el->getChildren());
  s << ' ' << children.size();
  for (List::const_iterator iter = children.begin(); iter != children.end(); ++iter)
    dumpElement(s, *iter);
  s << ')';
}

static string decodeHex(const string &line)
{
  string res;
  for (size_t index = 0; index + 1 < line.size(); index += 2) {
    int value = std::stoi(line.substr(index, 2), nullptr, 16);
    res.push_back((char)value);
  }
  return res;
}

int main(int argc, char **argv)
{
  string line;
  while (std::getline(std::cin, line)) {
    std::istringstream input(decodeHex(line));
    std::ostringstream out;
    try {
      Document *doc = xml_tree(input);
      dumpElement(out, doc->getRoot());
      delete doc;
    }
    catch (DecoderError &err) {
      out << "ERROR ";
      dumpString(out, err.explain);
    }
    std::cout << out.str() << '\n';
  }
  return 0;
}
