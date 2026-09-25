#include "libdecomp.hh"
#include "sleigh_arch.hh"
#include "sleigh.hh"

#include <fstream>
#include <iomanip>
#include <unistd.h>
#include <sys/wait.h>

namespace ghidra {

using std::cout;
using std::cerr;
using std::istreambuf_iterator;

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

class SleighAccess : public Sleigh {
public:
  ParserContext *pcodeContext(const Address &addr) const { return obtainContext(addr,ParserContext::pcode); }
};

static string probeDelaySlots(const Translate *translate,const SleighAccess *access,const Address &addr)

{
  ParserContext *position = access->pcodeContext(addr);
  int4 delayBytes = position->getDelaySlot();
  int4 fallOffset = position->getLength();
  int4 byteCount = 0;
  while(byteCount < delayBytes) {
    Address delayAddress = addr + fallOffset;
    ParserContext *delayPosition = access->pcodeContext(delayAddress);
    int4 delayLength = delayPosition->getLength();
    if (delayPosition->getDelaySlot() > 0) {
      string nested = probeDelaySlots(translate,access,delayAddress);
      if (!nested.empty()) return nested;
    }
    else {
      PcodeCapture scratch;
      try {
        translate->oneInstruction(scratch,delayAddress);
      }
      catch(UnimplError &err) {
        return err.explain;
      }
    }
    fallOffset += delayLength;
    byteCount += delayLength;
  }
  return "";
}

class ChildProbe {
public:
  virtual ~ChildProbe(void) {}
  virtual int4 work(string &message) = 0;
};

class RealTranslation : public ChildProbe {
  const Translate *translate;
  Address addr;
public:
  RealTranslation(const Translate *trans,const Address &address) { translate = trans; addr = address; }
  virtual int4 work(string &message) {
    PcodeCapture scratch;
    try {
      translate->oneInstruction(scratch,addr);
    }
    catch(UnimplError &err) {
      return 3;
    }
    catch(LowlevelError &err) {
      return 0;
    }
    return 0;
  }
};

class DelaySlotSearch : public ChildProbe {
  const Translate *translate;
  const SleighAccess *access;
  Address addr;
public:
  DelaySlotSearch(const Translate *trans,const SleighAccess *acc,const Address &address) { translate = trans; access = acc; addr = address; }
  virtual int4 work(string &message) {
    try {
      message = probeDelaySlots(translate,access,addr);
    }
    catch(LowlevelError &err) {
      message.clear();
    }
    return message.empty() ? 0 : 3;
  }
};

static int4 runInChild(ChildProbe &probe,string &message)

{
  cout.flush();
  int pipeEnds[2];
  if (pipe(pipeEnds) != 0)
    throw LowlevelError("pipe failed");
  pid_t child = fork();
  if (child < 0)
    throw LowlevelError("fork failed");
  if (child == 0) {
    close(pipeEnds[0]);
    string childMessage;
    int4 exitCode = probe.work(childMessage);
    if (!childMessage.empty()) {
      ssize_t written = write(pipeEnds[1],childMessage.data(),childMessage.size());
      if (written != (ssize_t)childMessage.size())
        exitCode = 4;
    }
    close(pipeEnds[1]);
    _exit(exitCode);
  }
  close(pipeEnds[1]);
  message.clear();
  char chunk[4096];
  for(;;) {
    ssize_t count = read(pipeEnds[0],chunk,sizeof(chunk));
    if (count <= 0) break;
    message.append(chunk,count);
  }
  close(pipeEnds[0]);
  int childStatus = 0;
  waitpid(child,&childStatus,0);
  if (WIFEXITED(childStatus))
    return WEXITSTATUS(childStatus);
  return -1;
}

static string unimplementedDelaySlot(const Translate *translate,const Address &addr)

{
  const SleighAccess *access = static_cast<const SleighAccess *>(static_cast<const Sleigh *>(translate));
  ParserContext *position = access->pcodeContext(addr);
  if (position->getDelaySlot() <= 0) return "";
  string message;
  RealTranslation real(translate,addr);
  int4 realStatus = runInChild(real,message);
  if (realStatus == 0) return "";
  DelaySlotSearch search(translate,access,addr);
  int4 searchStatus = runInChild(search,message);
  if (searchStatus == 3) return message;
  if (realStatus != 3)
    throw LowlevelError("pcode translation crashed");
  return "";
}

static bool readFile(const string &path,vector<uint1> &content)

{
  ifstream stream(path.c_str(),ios::binary);
  if (!stream) return false;
  content.assign(istreambuf_iterator<char>(stream),istreambuf_iterator<char>());
  return true;
}

static void printError(ostream &out,const Address &addr,const string &phase,const string &kind,const string &message)

{
  out << "E\t0x" << hex << addr.getOffset() << dec << '\t' << phase << '\t' << kind << '\t' << escapeText(message) << '\n';
}

static int4 listLanguages(void)

{
  const vector<LanguageDescription> &descriptions(SleighArchitecture::getDescriptions());
  for(int4 index=0;index<descriptions.size();++index) {
    const LanguageDescription &description(descriptions[index]);
    cout << description.getId() << '\t' << description.getSlaFile() << '\t' << description.getProcessorSpec();
    cout << '\t' << (description.isDeprecated() ? "deprecated" : "active") << '\n';
  }
  return 0;
}

static int4 dumpLanguage(const string &languageId,const string &inputPath,uintb base,const vector<pair<string,uintm> > &overrides)

{
  vector<uint1> content;
  if (!readFile(inputPath,content)) {
    cerr << "cannot read input file " << inputPath << endl;
    return 2;
  }
  ostream &out(cout);
  out << "language\t" << languageId << '\n';
  out << "base\t0x" << hex << base << dec << '\n';
  out << "size\t" << content.size() << '\n';
  for(int4 index=0;index<overrides.size();++index)
    out << "context\t" << overrides[index].first << '=' << overrides[index].second << '\n';

  ostringstream errorStream;
  DumpArchitecture *architecture = new DumpArchitecture(languageId + ":default",base,content,&errorStream);
  DocumentStorage store;
  try {
    architecture->init(store);
    AddrSpace *overrideSpace = architecture->translate->getDefaultCodeSpace();
    for(int4 index=0;index<overrides.size();++index) {
      architecture->context->setVariableDefault(overrides[index].first,overrides[index].second);
      architecture->context->setVariableRegion(overrides[index].first,Address(overrideSpace,0),Address(),overrides[index].second);
    }
  }
  catch(DecoderError &err) {
    out << "loaderror\tDecoderError\t" << escapeText(err.explain) << '\n';
    out.flush();
    return 1;
  }
  catch(LowlevelError &err) {
    out << "loaderror\tLowlevelError\t" << escapeText(err.explain) << '\n';
    out.flush();
    return 1;
  }
  const Translate *translate = architecture->translate;
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
      string delayFailure = unimplementedDelaySlot(translate,addr);
      if (!delayFailure.empty()) {
        failureKind = "UnimplError";
        failureMessage = delayFailure;
      }
      else
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
  out.flush();
  return 0;
}

}

int main(int argc,char **argv)

{
  using namespace ghidra;
  using std::cerr;
  using std::cout;
  if (argc < 3) {
    cerr << "usage: sleigh_dump <sleighhome> list" << endl;
    cerr << "       sleigh_dump <sleighhome> dump <languageid> <input.bin> <base> [name=value ...]" << endl;
    return 2;
  }
  startDecompilerLibrary(argv[1]);
  string command(argv[2]);
  int4 status = 2;
  if (command == "list")
    status = listLanguages();
  else if (command == "dump" && argc >= 6) {
    uintb base = strtoull(argv[5],(char **)0,0);
    vector<pair<string,uintm> > overrides;
    for(int4 index=6;index<argc;++index) {
      string setting(argv[index]);
      string::size_type position = setting.find('=');
      if (position == string::npos) {
        cerr << "bad context setting " << setting << endl;
        return 2;
      }
      overrides.push_back(make_pair(setting.substr(0,position),(uintm)strtoul(setting.c_str()+position+1,(char **)0,0)));
    }
    status = dumpLanguage(argv[3],argv[4],base,overrides);
  }
  else
    cerr << "unknown command " << command << endl;
  cout.flush();
  _exit(status);
}
