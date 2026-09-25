#include "grammar.hh"
#include <iostream>
#include <sstream>

using namespace ghidra;
using std::cin;
using std::cout;

static string unescape(const string &text)
{
  string result;
  for(size_t pos=0;pos<text.size();++pos) {
    if (text[pos] == '%' && pos + 2 < text.size()) {
      int val = std::stoi(text.substr(pos+1,2),nullptr,16);
      result += (char)val;
      pos += 2;
    }
    else
      result += text[pos];
  }
  return result;
}

static string escape(const string &text)
{
  string result;
  static const char digits[] = "0123456789abcdef";
  for(size_t pos=0;pos<text.size();++pos) {
    unsigned char byte = (unsigned char)text[pos];
    if (byte < 0x21 || byte >= 0x7f || byte == '%') {
      result += '%';
      result += digits[byte >> 4];
      result += digits[byte & 0xf];
    }
    else
      result += (char)byte;
  }
  return result;
}

int main(void)
{
  string line;
  while(getline(cin,line)) {
    size_t space = line.find(' ');
    int4 maxbuf = std::stoi(line.substr(0,space));
    string input = unescape(line.substr(space+1));
    istringstream s(input);
    GrammarLexer lexer(maxbuf);
    lexer.pushFile("stream",&s);
    ostringstream out;
    try {
    for(int4 count=0;count<200;++count) {
      GrammarToken tok;
      lexer.getNextToken(tok);
      uint4 tp = tok.getType();
      out << tp << ':' << tok.getLineNo() << ':' << tok.getColNo();
      if (tp == GrammarToken::integer || tp == GrammarToken::charconstant)
	out << ':' << std::hex << tok.getInteger() << std::dec;
      else if (tp == GrammarToken::identifier || tp == GrammarToken::stringval) {
	out << ':' << escape(*tok.getString());
	delete tok.getString();
      }
      out << ' ';
      if (tp == GrammarToken::endoffile || tp == GrammarToken::badtoken) break;
    }
    }
    catch(std::exception &err) {
      cout << "CRASH\n";
      continue;
    }
    out << "| " << lexer.getError();
    cout << out.str() << '\n';
  }
  return 0;
}
