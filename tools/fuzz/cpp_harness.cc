#include "libdecomp.hh"
#include "raw_arch.hh"
#include "sleigh_arch.hh"
#include "sleigh.hh"

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <unistd.h>

namespace ghidra {

class BufferLoadImage : public LoadImage {
  uintb baseOffset;
  vector<uint1> bytes;
public:
  BufferLoadImage(uintb base,const vector<uint1> &content) : LoadImage("buffer") { baseOffset = base; bytes = content; }
  virtual void loadFill(uint1 *ptr,int4 size,const Address &addr);
  virtual string getArchType(void) const { return "buffer"; }
  virtual void adjustVma(long adjust) {}
};

void BufferLoadImage::loadFill(uint1 *ptr,int4 size,const Address &addr)

{
  uintb start = addr.getOffset();
  for(int4 index=0;index<size;++index) {
    uintb current = start + index;
    if (current < baseOffset || current - baseOffset >= bytes.size())
      ptr[index] = 0;
    else
      ptr[index] = bytes[current - baseOffset];
  }
}

class DumpArchitecture : public SleighArchitecture {
  uintb baseOffset;
  vector<uint1> bytes;
  virtual void buildLoader(DocumentStorage &store);
  virtual void resolveArchitecture(void);
public:
  DumpArchitecture(const string &target,uintb base,const vector<uint1> &content,ostream *estream)
    : SleighArchitecture("buffer",target,estream) { baseOffset = base; bytes = content; }
};

void DumpArchitecture::buildLoader(DocumentStorage &store)

{
  collectSpecFiles(*errorstream);
  loader = new BufferLoadImage(baseOffset,bytes);
}

void DumpArchitecture::resolveArchitecture(void)

{
  archid = getTarget();
  SleighArchitecture::resolveArchitecture();
}

static string escapeText(const string &text)

{
  string result;
  for(string::size_type index=0;index<text.size();++index) {
    char character = text[index];
    if (character == '\n')
      result += "\\n";
    else if (character == '\t')
      result += "\\t";
    else if (character == '\r')
      result += "\\r";
    else
      result += character;
  }
  return result;
}

class AssemblyCapture : public AssemblyEmit {
public:
  string mnemonic;
  string body;
  virtual void dump(const Address &addr,const string &mnem,const string &bodytext) { mnemonic = mnem; body = bodytext; }
};

class PcodeCapture : public PcodeEmit {
public:
  vector<string> lines;
  virtual void dump(const Address &addr,OpCode opc,VarnodeData *outvar,VarnodeData *vars,int4 isize);
};

static void printVarnode(ostream &stream,const VarnodeData &data,bool spaceOperand)

{
  stream << '(' << data.space->getName() << ',';
  if (spaceOperand) {
    AddrSpace *referenced = data.getSpaceFromConst();
    stream << "space:" << referenced->getName();
  }
  else
    stream << "0x" << hex << data.offset << dec;
  stream << ',' << dec << data.size << ')';
}

void PcodeCapture::dump(const Address &addr,OpCode opc,VarnodeData *outvar,VarnodeData *vars,int4 isize)

{
  ostringstream stream;
  if (outvar != (VarnodeData *)0) {
    printVarnode(stream,*outvar,false);
    stream << " = ";
  }
  stream << get_opname(opc);
  for(int4 slot=0;slot<isize;++slot) {
    stream << ' ';
    bool spaceOperand = (slot == 0) && (opc == CPUI_LOAD || opc == CPUI_STORE);
    printVarnode(stream,vars[slot],spaceOperand);
  }
  lines.push_back(stream.str());
}

static void printError(ostream &out,const Address &addr,const string &phase,const string &kind,const string &message)

{
  out << "E\t0x" << hex << addr.getOffset() << dec << '\t' << phase << '\t' << kind << '\t' << escapeText(message) << '\n';
}

static string sleighDump(const string &languageId,const vector<uint1> &content,uintb base)

{
  ostringstream out;
  out << "language\t" << languageId << '\n';
  out << "base\t0x" << hex << base << dec << '\n';
  out << "size\t" << content.size() << '\n';
  ostringstream errorStream;
  DumpArchitecture architecture(languageId + ":default",base,content,&errorStream);
  DocumentStorage store;
  try {
    architecture.init(store);
  }
  catch(DecoderError &err) {
    out << "loaderror\tDecoderError\t" << escapeText(err.explain) << '\n';
    return out.str();
  }
  catch(LowlevelError &err) {
    out << "loaderror\tLowlevelError\t" << escapeText(err.explain) << '\n';
    return out.str();
  }
  const Translate *translate = architecture.translate;
  int4 alignment = translate->getAlignment();
  if (alignment < 1) alignment = 1;
  out << "alignment\t" << alignment << '\n';
  AddrSpace *codeSpace = translate->getDefaultCodeSpace();
  out << "codespace\t" << codeSpace->getName() << '\t' << codeSpace->getWordSize() << '\n';
  uintb endOffset = base + content.size();
  Address addr(codeSpace,base);
  while(addr.getOffset() >= base && addr.getOffset() < endOffset) {
    AssemblyCapture assembly;
    int4 assemblyLength = 0;
    string failureKind;
    string failureMessage;
    try {
      assemblyLength = translate->printAssembly(assembly,addr);
    }
    catch(UnimplError &err) { failureKind = "UnimplError"; failureMessage = err.explain; }
    catch(BadDataError &err) { failureKind = "BadDataError"; failureMessage = err.explain; }
    catch(LowlevelError &err) { failureKind = "LowlevelError"; failureMessage = err.explain; }
    if (!failureKind.empty() || assemblyLength <= 0) {
      if (failureKind.empty()) {
        failureKind = "LowlevelError";
        failureMessage = "non-positive instruction length";
      }
      printError(out,addr,"assembly",failureKind,failureMessage);
      uintb next = (addr.getOffset() / alignment + 1) * alignment;
      addr = Address(codeSpace,next);
      continue;
    }
    out << "I\t0x" << hex << addr.getOffset() << dec << '\t' << assemblyLength << '\t'
        << escapeText(assembly.mnemonic) << '\t' << escapeText(assembly.body) << '\n';
    PcodeCapture pcode;
    int4 pcodeLength = 0;
    try {
      pcodeLength = translate->oneInstruction(pcode,addr);
    }
    catch(UnimplError &err) { failureKind = "UnimplError"; failureMessage = err.explain; }
    catch(BadDataError &err) { failureKind = "BadDataError"; failureMessage = err.explain; }
    catch(LowlevelError &err) { failureKind = "LowlevelError"; failureMessage = err.explain; }
    if (!failureKind.empty())
      printError(out,addr,"pcode",failureKind,failureMessage);
    else {
      for(int4 index=0;index<pcode.lines.size();++index)
        out << "P\t" << pcode.lines[index] << '\n';
      out << "L\t" << pcodeLength << '\n';
    }
    addr = addr + assemblyLength;
  }
  out << "end\n";
  return out.str();
}

static string decompileRaw(const string &languageId,const vector<uint1> &content)

{
  string path = "/dev/shm/ghidra_fuzz_" + to_string(getpid()) + ".bin";
  {
    std::ofstream image(path.c_str(),std::ios::binary | std::ios::trunc);
    image.write((const char *)content.data(),content.size());
  }
  ostringstream errorStream;
  RawBinaryArchitecture *architecture = new RawBinaryArchitecture(path,languageId,&errorStream);
  string result;
  try {
    DocumentStorage store;
    architecture->init(store);
    Address addr(architecture->getDefaultCodeSpace(),0);
    string name;
    architecture->nameFunction(addr,name);
    Funcdata *fd = architecture->symboltab->getGlobalScope()->addFunction(addr,name)->getFunction();
    if (fd->hasNoCode())
      result = "error: No code for " + fd->getName();
    else {
      Action *action = architecture->allacts.getCurrent();
      action->reset(*fd);
      action->perform(*fd);
      ostringstream text;
      architecture->print->setOutputStream(&text);
      architecture->print->docFunction(fd);
      result = text.str();
    }
  }
  catch(LowlevelError &err) {
    result = "error: " + err.explain;
  }
  catch(DecoderError &err) {
    result = "error: " + err.explain;
  }
  delete architecture;
  return result;
}

static void ensureStarted(void)

{
  static bool started = false;
  if (started) return;
  const char *home = getenv("SLEIGHHOME");
  startDecompilerLibrary(home == (const char *)0 ? "" : home);
  started = true;
}

static char *copyOut(const string &text)

{
  char *buffer = (char *)malloc(text.size() + 1);
  memcpy(buffer,text.c_str(),text.size() + 1);
  return buffer;
}

}

using namespace ghidra;

extern "C" char *ghidra_cpp_sleigh_dump(const char *language,const uint8_t *data,size_t size,uint64_t base)

{
  ensureStarted();
  vector<uint1> content(data,data + size);
  return copyOut(sleighDump(language,content,base));
}

extern "C" char *ghidra_cpp_decompile(const char *language,const uint8_t *data,size_t size)

{
  ensureStarted();
  vector<uint1> content(data,data + size);
  return copyOut(decompileRaw(language,content));
}

extern "C" void ghidra_cpp_free(char *text)

{
  free(text);
}
