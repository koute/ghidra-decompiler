#include "sleigh.hh"
#include "pcodeparse.hh"
#include "loadimage.hh"
#include <iostream>
#include <sstream>
#include <map>

using namespace ghidra;
using std::cout;
using std::cin;
using std::endl;

class NullLoadImage : public LoadImage {
public:
  NullLoadImage(void) : LoadImage("null") {}
  virtual void loadFill(uint1 *ptr,int4 size,const Address &addr) { for(int4 i=0;i<size;++i) ptr[i] = 0; }
  virtual string getArchType(void) const { return "null"; }
  virtual void adjustVma(long adjust) {}
};

static string unescape(const string &text)

{
  string res;
  for(size_t i=0;i<text.size();++i) {
    if (text[i] == '\\' && i + 3 < text.size() && text[i+1] == 'x') {
      string hexdigits = text.substr(i+2,2);
      res += (char)strtol(hexdigits.c_str(),(char **)0,16);
      i += 3;
    }
    else
      res += text[i];
  }
  return res;
}

static string escape(const string &text)

{
  std::ostringstream s;
  for(size_t i=0;i<text.size();++i) {
    unsigned char c = (unsigned char)text[i];
    if (c < 0x20 || c >= 0x7f || c == '\\') {
      static const char *digits = "0123456789abcdef";
      s << "\\x" << digits[c >> 4] << digits[c & 15];
    }
    else
      s << (char)c;
  }
  return s.str();
}

struct Language {
  NullLoadImage loader;
  ContextInternal context;
  Sleigh *sleigh;
};

int main(int argc,char **argv)

{
  if (argc < 2) {
    std::cerr << "usage: pcodeparse_probe <languages-dir> < cases" << endl;
    return 2;
  }
  string root(argv[1]);
  std::map<string,Language *> languages;
  string line;
  while(getline(cin,line)) {
    std::vector<string> fields;
    size_t start = 0;
    for(;;) {
      size_t pos = line.find('\t',start);
      if (pos == string::npos) { fields.push_back(line.substr(start)); break; }
      fields.push_back(line.substr(start,pos-start));
      start = pos + 1;
    }
    if (fields.size() != 4) {
      cout << "BAD" << endl;
      continue;
    }
    Language *lang;
    std::map<string,Language *>::iterator iter = languages.find(fields[0]);
    if (iter == languages.end()) {
      lang = new Language();
      lang->sleigh = new Sleigh(&lang->loader,&lang->context);
      DocumentStorage store;
      std::istringstream s("<sleigh>" + root + "/" + fields[0] + "</sleigh>");
      Document *doc = store.parseDocument(s);
      store.registerTag(doc->getRoot());
      lang->sleigh->initialize(store);
      languages[fields[0]] = lang;
    }
    else
      lang = (*iter).second;
    uint4 base = (uint4)strtoul(fields[1].c_str(),(char **)0,16);
    try {
      PcodeSnippet compiler(lang->sleigh);
      if (fields[2] != "-") {
        int4 index = 0;
        size_t pos = 0;
        for(;;) {
          size_t comma = fields[2].find(',',pos);
          string name = fields[2].substr(pos,comma == string::npos ? string::npos : comma - pos);
          compiler.addOperand(name,index);
          index += 1;
          if (comma == string::npos) break;
          pos = comma + 1;
        }
      }
      compiler.setUniqueBase(base);
      std::istringstream s(unescape(fields[3]));
      if (!compiler.parseStream(s)) {
        cout << "ERR\t" << escape(compiler.getErrorMessage()) << endl;
        continue;
      }
      ConstructTpl *tpl = compiler.releaseResult();
      std::ostringstream xml;
      XmlEncode encoder(xml,false);
      tpl->encode(encoder,-1);
      delete tpl;
      cout << "OK\t" << std::hex << compiler.getUniqueBase() << std::dec << '\t' << escape(compiler.getErrorMessage()) << '\t' << xml.str() << endl;
    }
    catch(LowlevelError &err) {
      cout << "EXC\t" << escape(err.explain) << endl;
    }
  }
  return 0;
}
