#include "libdecomp.hh"
#include "architecture.hh"
#include "grammar.hh"
#include <iostream>
#include <sstream>

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

static string describe(Datatype *ct,int4 depth)
{
  if (ct == (Datatype *)0) return "null";
  ostringstream s;
  s << ct->getName() << ':' << (int4)ct->getMetatype() << ':' << ct->getSize();
  if (depth > 3) return s.str();
  if (ct->getMetatype() == TYPE_PTR)
    s << "->" << describe(((TypePointer *)ct)->getPtrTo(),depth+1);
  else if (ct->getMetatype() == TYPE_ARRAY)
    s << '[' << ((TypeArray *)ct)->numElements() << ']' << describe(((TypeArray *)ct)->getBase(),depth+1);
  else if (ct->getMetatype() == TYPE_STRUCT) {
    const TypeStruct *st = (const TypeStruct *)ct;
    s << '{';
    for(vector<TypeField>::const_iterator iter=st->beginField();iter!=st->endField();++iter)
      s << (*iter).name << '@' << (*iter).offset << '=' << describe((*iter).type,depth+1) << ';';
    s << '}';
  }
  else if (ct->getMetatype() == TYPE_CODE) {
    const FuncProto *proto = ((TypeCode *)ct)->getPrototype();
    if (proto != (const FuncProto *)0) {
      s << '(' << proto->numParams() << (proto->isDotdotdot() ? "..." : "") << ")->" << describe(proto->getOutputType(),depth+1);
    }
  }
  return s.str();
}

int main(int argc,char **argv)
{
  startDecompilerLibrary(argv[1]);
  ArchitectureCapability *xmlCapability = ArchitectureCapability::getCapability("xml");
  istringstream archstream("<binaryimage arch=\"x86:LE:64:default:gcc\"></binaryimage>");
  DocumentStorage store;
  Document *doc = store.parseDocument(archstream);
  store.registerTag(doc->getRoot());
  ostringstream errs;
  Architecture *glb = xmlCapability->buildArchitecture("", "", &errs);
  glb->init(store);
  string line;
  while(getline(cin,line)) {
    char kind = line[0];
    string text = line.substr(2);
    istringstream s(text);
    try {
      if (kind == 'T') {
	string name;
	Datatype *ct = parse_type(s,name,glb);
	cout << "OK " << name << ' ' << escape(describe(ct,0)) << '\n';
      }
      else if (kind == 'P') {
	PrototypePieces pieces;
	parse_protopieces(pieces,s,glb);
	cout << "OK " << (pieces.model == (ProtoModel *)0 ? string("none") : pieces.model->getName()) << ' ' << pieces.name;
	cout << ' ' << escape(describe(pieces.outtype,0)) << ' ' << pieces.firstVarArgSlot;
	for(int4 i=0;i<pieces.intypes.size();++i)
	  cout << ' ' << pieces.innames[i] << '=' << escape(describe(pieces.intypes[i],0));
	cout << '\n';
      }
      else if (kind == 'C') {
	parse_C(glb,s);
	cout << "OK\n";
      }
    }
    catch(LowlevelError &err) {
      cout << "ERR " << escape(err.explain) << '\n';
    }
  }
  return 0;
}
