#include <iostream>
#include <sstream>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <list>
#include <string>
#include <algorithm>
#include <unordered_map>
#include <memory>
#include <functional>
#include <iomanip>
#include <cstring>
#include <array>
#include <bitset>
#include <deque>
#include <stack>
#include <queue>
#define protected public
#include "libdecomp.hh"
#include "architecture.hh"
#include "grammar.hh"
#undef protected

using namespace ghidra;
using std::cin;
using std::cout;

static string escape(const string &text)
{
  string result;
  static const char digits[] = "0123456789abcdef";
  for(size_t pos=0;pos<text.size();++pos) {
    unsigned char byte = (unsigned char)text[pos];
    if (byte < 0x20 || byte >= 0x7f || byte == '%') {
      result += '%';
      result += digits[byte >> 4];
      result += digits[byte & 0xf];
    }
    else
      result += (char)byte;
  }
  return result;
}

static Architecture *buildArch(void)
{
  ArchitectureCapability *xmlCapability = ArchitectureCapability::getCapability("xml");
  istringstream archstream("<binaryimage arch=\"x86:LE:64:default:gcc\"></binaryimage>");
  DocumentStorage store;
  Document *doc = store.parseDocument(archstream);
  store.registerTag(doc->getRoot());
  ostringstream *errs = new ostringstream();
  Architecture *glb = xmlCapability->buildArchitecture("", "", errs);
  glb->init(store);
  return glb;
}

int main(int argc,char **argv)
{
  startDecompilerLibrary(argv[1]);
  string line;
  while(getline(cin,line)) {
    istringstream fields(line);
    int4 markup, linewidth, indent;
    string language, comments, integers;
    fields >> markup >> linewidth >> indent >> language >> comments >> integers;
    string rest;
    getline(fields,rest);
    Architecture *glb = buildArch();
    ostringstream result;
    try {
      if (language == "java") {
	glb->setPrintLanguage("java-language");
      }
      size_t pos = 0;
      while(pos <= rest.size()) {
	size_t next = rest.find('|',pos);
	if (next == string::npos) next = rest.size();
	string def = rest.substr(pos,next-pos);
	pos = next + 1;
	if (def.find_first_not_of(' ') == string::npos) continue;
	istringstream s(def);
	parse_C(glb,s);
      }
      ostringstream out;
      glb->print->setOutputStream(&out);
      if (markup != 0) {
	glb->print->setMarkup(true);
	glb->print->setPackedOutput(false);
      }
      glb->print->setMaxLineSize(linewidth);
      glb->print->setIndentIncrement(indent);
      glb->print->setCommentStyle(comments);
      glb->print->setIntegerFormat(integers);
      int4 id = glb->print->emit->beginDocument();
      glb->print->docTypeDefinitions(glb->types);
      glb->print->emit->endDocument(id);
      glb->print->emit->flush();
      result << "OUT " << escape(out.str());
    }
    catch(LowlevelError &err) {
      result << "ERR " << escape(err.explain);
    }
    cout << result.str() << '\n';
    delete glb;
  }
  return 0;
}
