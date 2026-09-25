#include "translate.hh"
#include "globalcontext.hh"
#include <iostream>
#include <sstream>
#include <cstring>
#include <cmath>

using namespace ghidra;

static const char *SPACES_XML =
  "<spaces defaultspace=\"ram\">"
  "<space_other name=\"OTHER\" index=\"1\" size=\"8\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>"
  "<space name=\"ram\" index=\"2\" size=\"8\" bigendian=\"false\" delay=\"1\" deadcodedelay=\"2\" physical=\"true\"/>"
  "<space name=\"register\" index=\"3\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>"
  "<space_unique name=\"unique\" index=\"4\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>"
  "<space name=\"bram\" index=\"5\" size=\"4\" bigendian=\"true\" delay=\"1\" physical=\"true\"/>"
  "<space name=\"code16\" index=\"6\" size=\"2\" wordsize=\"2\" bigendian=\"false\" delay=\"1\" physical=\"true\"/>"
  "<space name=\"data4\" index=\"7\" size=\"3\" wordsize=\"4\" bigendian=\"true\" delay=\"1\" physical=\"true\"/>"
  "<space_base name=\"stack\" index=\"8\" size=\"8\" bigendian=\"false\" delay=\"1\" physical=\"true\" contain=\"ram\"/>"
  "<space_overlay name=\"ovl\" index=\"9\" base=\"ram\"/>"
  "<space name=\"Tiny\" index=\"10\" size=\"1\" bigendian=\"false\" delay=\"1\" physical=\"true\"/>"
  "<space name=\"register2\" index=\"11\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>"
  "<space name=\"rom\" index=\"12\" size=\"6\" bigendian=\"true\" delay=\"1\" physical=\"false\"/>"
  "</spaces>";

class ProbeTranslate : public Translate {
public:
  map<string,VarnodeData> regs;
  void setup(void) {
    std::istringstream s(SPACES_XML);
    XmlDecode decoder(this);
    decoder.ingestStream(s);
    decodeSpaces(decoder,this);
    insertSpace(new JoinSpace(this,this,13));
    AddrSpace *reg = getSpaceByName("register");
    AddrSpace *bram = getSpaceByName("bram");
    addReg("eax",reg,0,4);
    addReg("ax",reg,0,2);
    addReg("ebx",reg,4,4);
    addReg("ecx",reg,8,4);
    addReg("edx",reg,0xc,4);
    addReg("rdx",reg,0x8,8);
    addReg("sp",reg,0x20,8);
    addReg("hi",bram,0x100,4);
    addReg("lo",bram,0x104,4);
    addReg("hilo",bram,0x100,8);
    VarnodeData spvn = regs["sp"];
    addSpacebasePointer((SpacebaseSpace *)getSpaceByName("stack"),spvn,8,true);
  }
  void addReg(const string &nm,AddrSpace *spc,uintb off,uint4 sz) {
    VarnodeData vn; vn.space = spc; vn.offset = off; vn.size = sz; regs[nm] = vn;
  }
  void truncate(const string &nm,uint4 sz) {
    std::ostringstream s;
    s << "<truncate_space space=\"" << nm << "\" size=\"" << sz << "\"/>";
    std::istringstream in(s.str());
    XmlDecode decoder(this);
    decoder.ingestStream(in);
    TruncationTag tag;
    tag.decode(decoder);
    truncateSpace(tag);
  }
  void nearPointers(AddrSpace *spc,int4 sz) { markNearPointers(spc,sz); }
  void noHighPtr(const Range &rng) { addNoHighPtr(rng); }
  void inferBounds(const Range &rng) { setInferPtrBounds(rng); }
  virtual void initialize(DocumentStorage &store) {}
  virtual const VarnodeData &getRegister(const string &nm) const {
    map<string,VarnodeData>::const_iterator iter = regs.find(nm);
    if (iter == regs.end()) throw LowlevelError("Cannot add register to DummyTranslate");
    return (*iter).second;
  }
  virtual string getRegisterName(AddrSpace *base,uintb off,int4 size) const {
    map<string,VarnodeData>::const_iterator iter;
    for(iter=regs.begin();iter!=regs.end();++iter) {
      const VarnodeData &vn((*iter).second);
      if (vn.space == base && vn.offset == off && (int4)vn.size == size) return (*iter).first;
    }
    return "";
  }
  virtual string getExactRegisterName(AddrSpace *base,uintb off,int4 size) const { return getRegisterName(base,off,size); }
  virtual void getAllRegisters(map<VarnodeData,string> &reglist) const {}
  virtual void getUserOpNames(vector<string> &res) const {}
  virtual int4 instructionLength(const Address &baseaddr) const { return -1; }
  virtual int4 oneInstruction(PcodeEmit &emit,const Address &baseaddr) const { return -1; }
  virtual int4 printAssembly(AssemblyEmit &emit,const Address &baseaddr) const { return -1; }
};

static string unhex(const string &text)
{
  string res;
  if (text == "-") return res;
  for (size_t index = 0; index + 1 < text.size(); index += 2)
    res.push_back((char)std::stoi(text.substr(index,2),nullptr,16));
  return res;
}

static string tohex(const string &text)
{
  static const char *digits = "0123456789abcdef";
  string res;
  for (size_t index = 0; index < text.size(); ++index) {
    unsigned char byte = (unsigned char)text[index];
    res.push_back(digits[byte >> 4]);
    res.push_back(digits[byte & 15]);
  }
  return res;
}

static uintb num(std::istream &s)
{
  string tok;
  s >> tok;
  return std::stoull(tok,nullptr,16);
}

static int4 inum(std::istream &s)
{
  string tok;
  s >> tok;
  return (int4)std::stol(tok,nullptr,10);
}

static string word(std::istream &s)
{
  string tok;
  s >> tok;
  return tok;
}

static double bitsToDouble(uintb bits)
{
  double res;
  memcpy(&res,&bits,8);
  return res;
}

static uintb doubleToBits(double val)
{
  uintb res;
  memcpy(&res,&val,8);
  return res;
}

static AttributeId *attribByName(const string &nm)
{
  static AttributeId *table[] = { &ATTRIB_ALIGN, &ATTRIB_BIGENDIAN, &ATTRIB_NAME, &ATTRIB_SIZE, &ATTRIB_SPACE, &ATTRIB_VAL,
				  &ATTRIB_VALUE, &ATTRIB_OFFSET, &ATTRIB_PIECE, &ATTRIB_FORMAT, &ATTRIB_ID, &ATTRIB_CONTENT,
				  &ATTRIB_STORAGE, &ATTRIB_UNKNOWN, &ATTRIB_CODE };
  for(int4 i=0;i<sizeof(table)/sizeof(table[0]);++i)
    if (table[i]->getName() == nm) return table[i];
  return &ATTRIB_UNKNOWN;
}

struct AttrSpec {
  char type;
  string name;
  string value;
};

static vector<AttrSpec> parseSpec(const string &text)
{
  vector<AttrSpec> res;
  size_t pos = 0;
  while(pos < text.size()) {
    size_t end = text.find(';',pos);
    if (end == string::npos) end = text.size();
    string item = text.substr(pos,end-pos);
    pos = end + 1;
    if (item.size() < 3) continue;
    AttrSpec spec;
    spec.type = item[0];
    size_t eq = item.find('=',2);
    spec.name = item.substr(2,eq-2);
    spec.value = (eq == string::npos) ? string() : item.substr(eq+1);
    res.push_back(spec);
  }
  return res;
}

static void encodeSpec(Encoder &enc,const vector<AttrSpec> &specs,AddrSpaceManager *manage)
{
  enc.openElement(ELEM_DATA);
  for(int4 i=0;i<specs.size();++i) {
    const AttrSpec &spec(specs[i]);
    AttributeId *attrib = attribByName(spec.name);
    switch(spec.type) {
      case 'S': enc.writeSignedInteger(*attrib,(intb)std::stoull(spec.value,nullptr,16)); break;
      case 'U': enc.writeUnsignedInteger(*attrib,std::stoull(spec.value,nullptr,16)); break;
      case 'B': enc.writeBool(*attrib,spec.value == "1"); break;
      case 'T': enc.writeString(*attrib,spec.value); break;
      case 'P': enc.writeSpace(*attrib,manage->getSpace(std::stoi(spec.value))); break;
      case 'O': enc.writeOpcode(*attrib,(OpCode)std::stoi(spec.value)); break;
      case 'I': enc.writeStringIndexed(*attrib,std::stoi(spec.value.substr(0,1)),spec.value.substr(1)); break;
    }
  }
  enc.openElement(ELEM_VAL);
  enc.closeElement(ELEM_VAL);
  enc.closeElement(ELEM_DATA);
}

static string readOne(Decoder &dec,char type,AttributeId *attrib)
{
  std::ostringstream out;
  try {
    switch(type) {
      case 'S': out << std::hex << (uintb)(attrib ? dec.readSignedInteger(*attrib) : dec.readSignedInteger()); break;
      case 'U': out << std::hex << (attrib ? dec.readUnsignedInteger(*attrib) : dec.readUnsignedInteger()); break;
      case 'B': out << (attrib ? dec.readBool(*attrib) : dec.readBool()); break;
      case 'T': out << tohex(attrib ? dec.readString(*attrib) : dec.readString()); break;
      case 'P': out << (attrib ? dec.readSpace(*attrib) : dec.readSpace())->getName(); break;
      case 'O': out << get_opname(attrib ? dec.readOpcode(*attrib) : dec.readOpcode()); break;
      case 'E': out << std::hex << (uintb)(attrib ? dec.readSignedIntegerExpectString(*attrib,"hello",0x99) : dec.readSignedIntegerExpectString("hello",0x99)); break;
      case 'I': out << dec.getIndexedAttributeId(ATTRIB_PIECE); break;
      default: out << "skip"; break;
    }
  } catch(DecoderError &err) { out << "DERR:" << tohex(err.explain); }
  catch(LowlevelError &err) { out << "LERR:" << tohex(err.explain); }
  return out.str();
}

static string decodeSpec(Decoder &dec,const string &data,const string &reads,const vector<AttrSpec> &specs)
{
  std::ostringstream out;
  try {
    std::istringstream in(data);
    dec.ingestStream(in);
    uint4 el = dec.openElement(ELEM_DATA);
    size_t index = 0;
    for(;;) {
      uint4 id = dec.getNextAttributeId();
      if (id == 0) break;
      char type = (index < reads.size()) ? reads[index] : 'X';
      index += 1;
      out << id << '=' << readOne(dec,type,(AttributeId *)0) << ',';
    }
    out << '|';
    for(size_t i=0;i<specs.size();++i) {
      char type = (i < reads.size()) ? reads[i] : 'X';
      if (type == 'I') continue;
      out << readOne(dec,type,attribByName(specs[i].name)) << ',';
    }
    out << '|' << dec.peekElement();
    uint4 child = dec.openElement();
    out << ' ' << child;
    dec.closeElement(child);
    dec.closeElement(el);
    out << " done";
  } catch(DecoderError &err) { out << " DERR:" << tohex(err.explain); }
  catch(LowlevelError &err) { out << " LERR:" << tohex(err.explain); }
  return out.str();
}

class PrintEmit : public PcodeEmit {
public:
  std::ostringstream out;
  virtual void dump(const Address &addr,OpCode opc,VarnodeData *outvar,VarnodeData *vars,int4 isize) {
    out << get_opname(opc);
    if (outvar != (VarnodeData *)0) { out << " out="; outvar->getAddr().printRaw(out); out << ':' << std::dec << outvar->size; }
    for(int4 i=0;i<isize;++i) { out << " in="; vars[i].getAddr().printRaw(out); out << ':' << std::dec << vars[i].size; }
  }
};

class Probe {
  ProbeTranslate trans;
  RangeList rangelist;
  ContextInternal context;
  ContextCache *cache;
  TrackedSet *lastSet;
  AddrSpace *spc(std::istream &s) { return trans.getSpace(inum(s)); }
  Address addr(std::istream &s) { AddrSpace *sp = spc(s); uintb off = num(s); return Address(sp,off); }
public:
  Probe(void) { trans.setup(); lastSet = (TrackedSet *)0; cache = new ContextCache(&context); }
  string run(const string &cmd,std::istream &s);
};

string Probe::run(const string &cmd,std::istream &s)
{
  std::ostringstream out;
  if (cmd == "space") {
    AddrSpace *sp = spc(s);
    out << sp->getName() << ' ' << sp->getType() << ' ' << sp->getShortcut() << ' ' << sp->getIndex() << ' '
	<< sp->getAddrSize() << ' ' << sp->getWordSize() << ' ' << std::hex << sp->getHighest() << ' '
	<< sp->getPointerLowerBound() << ' ' << sp->getPointerUpperBound() << std::dec << ' ' << sp->getDelay() << ' '
	<< sp->getDeadcodeDelay() << ' ' << sp->getMinimumPtrSize() << ' ' << sp->isBigEndian() << sp->isHeritaged()
	<< sp->doesDeadcode() << sp->hasPhysical() << sp->isReverseJustified() << sp->isFormalStackSpace()
	<< sp->isOverlay() << sp->isOverlayBase() << sp->isOtherSpace() << sp->isTruncated() << sp->noHighPtrPossible()
	<< sp->hasNearPointers() << sp->allowsWrappedRange() << ' ' << sp->numSpacebase() << ' '
	<< sp->stackGrowsNegative() << ' ' << (sp->getContain() == (AddrSpace *)0 ? string("none") : sp->getContain()->getName());
  }
  else if (cmd == "shortcut") {
    char sc = (char)num(s);
    AddrSpace *sp = trans.getSpaceByShortcut(sc);
    out << (sp == (AddrSpace *)0 ? string("none") : sp->getName());
  }
  else if (cmd == "printraw") {
    Address a = addr(s);
    a.printRaw(out);
  }
  else if (cmd == "wrap") {
    AddrSpace *sp = spc(s);
    out << std::hex << sp->wrapOffset(num(s));
  }
  else if (cmd == "add") {
    Address a = addr(s);
    int8 off = (int8)num(s);
    Address b = a + off;
    Address c = a - off;
    b.printRaw(out); out << ' '; c.printRaw(out);
  }
  else if (cmd == "read") {
    AddrSpace *sp = spc(s);
    string text = unhex(word(s));
    try {
      Address a(sp,0);
      int4 sz = a.read(text);
      out << std::hex << a.getOffset() << std::dec << ' ' << sz;
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "overlap") {
    Address a = addr(s); int4 skip = inum(s); Address b = addr(s); int4 sz = inum(s);
    out << a.overlap(skip,b,sz);
    try { out << ' ' << a.overlapJoin(skip,b,sz); } catch(LowlevelError &err) { out << " ERROR " << err.explain; }
  }
  else if (cmd == "justified") {
    Address a = addr(s); int4 sz = inum(s); Address b = addr(s); int4 sz2 = inum(s); int4 force = inum(s);
    out << a.justifiedContain(sz,b,sz2,force != 0) << ' ' << a.containedBy(sz,b,sz2) << ' '
	<< a.isContiguous(sz,b,sz2) << ' ' << (a < b) << (a <= b) << (a == b) << (a != b);
  }
  else if (cmd == "validrange") {
    Address a = addr(s);
    out << a.isValidRange(num(s));
  }
  else if (cmd == "join") {
    int4 count = inum(s);
    vector<VarnodeData> pieces(count);
    for(int4 i=0;i<count;++i) { pieces[i].space = spc(s); pieces[i].offset = num(s); pieces[i].size = inum(s); }
    uint4 logical = inum(s);
    try {
      JoinRecord *rec = trans.findAddJoin(pieces,logical);
      Address a = rec->getUnified().getAddr();
      out << std::hex << a.getOffset() << std::dec << ' ' << rec->getUnified().size << ' ';
      a.printRaw(out);
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "joinequiv") {
    uintb off = num(s);
    uintb query = num(s);
    try {
      JoinRecord *rec = trans.findJoin(off);
      int4 pos = -7;
      Address a = rec->getEquivalentAddress(query,pos);
      a.printRaw(out);
      if (!a.isInvalid()) out << ' ' << pos;
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "renorm") {
    Address a = addr(s); int4 sz = inum(s);
    try { a.renormalize(sz); a.printRaw(out); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "cjoin") {
    Address a = addr(s); int4 sz = inum(s); Address b = addr(s); int4 sz2 = inum(s);
    try { Address r = trans.constructJoinAddress(&trans,a,sz,b,sz2); r.printRaw(out); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "cwrap") {
    Address a = addr(s); int4 sz = inum(s);
    try { Address r = trans.constructWrappingAddress(a,sz); r.printRaw(out); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "cfloat") {
    Address a = addr(s); int4 sz = inum(s); int4 lsz = inum(s);
    try { Address r = trans.constructFloatExtensionAddress(a,sz,lsz); r.printRaw(out); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "strip") {
    uintb off = num(s); int4 index = inum(s);
    try {
      JoinRecord *rec = trans.findJoin(off);
      const VarnodeData &vn(trans.stripJoinPiece(rec,index));
      vn.getAddr().printRaw(out); out << ' ' << vn.size;
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "encode") {
    Address a = addr(s); int4 sz = inum(s);
    try {
      std::ostringstream xs;
      XmlEncode xenc(xs);
      std::ostringstream ps;
      PackedEncode penc(ps);
      if (sz < 0) { a.encode(xenc); a.encode(penc); }
      else { a.encode(xenc,sz); a.encode(penc,sz); }
      out << tohex(xs.str()) << ' ' << tohex(ps.str());
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "decode") {
    int4 packed = inum(s);
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      int4 sz = -1;
      Address a;
      if (packed) { PackedDecode dec(&trans); dec.ingestStream(in); a = Address::decode(dec,sz); }
      else { XmlDecode dec(&trans); dec.ingestStream(in); a = Address::decode(dec,sz); }
      a.printRaw(out); out << ' ' << sz;
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "parse") {
    string text = unhex(word(s));
    try { Address a = trans.parseAddressSimple(text); a.printRaw(out); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "truncate") {
    string nm = unhex(word(s)); int4 sz = inum(s);
    try { trans.truncate(nm,sz); out << "ok"; } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "nearptr") {
    AddrSpace *sp = spc(s); int4 sz = inum(s);
    trans.nearPointers(sp,sz); out << "ok";
  }
  else if (cmd == "nohighptr") {
    AddrSpace *sp = spc(s); uintb first = num(s); uintb last = num(s);
    trans.noHighPtr(Range(sp,first,last)); out << "ok";
  }
  else if (cmd == "highptr") {
    Address a = addr(s); int4 sz = inum(s);
    out << trans.highPtrPossible(a,sz);
  }
  else if (cmd == "nextspace") {
    int4 ind = inum(s);
    AddrSpace *sp = (ind < 0) ? (AddrSpace *)0 : trans.getSpace(ind);
    AddrSpace *res = trans.getNextSpaceInOrder(sp);
    if (res == (AddrSpace *)0) out << "null";
    else if (res == (AddrSpace *) ~((uintp)0)) out << "max";
    else out << res->getName();
  }
  else if (cmd == "lastopen") {
    AddrSpace *sp = spc(s); uintb first = num(s); uintb last = num(s);
    Address a = Range(sp,first,last).getLastAddrOpen(&trans);
    if (a.getSpace() == (AddrSpace *) ~((uintp)0)) out << "max " << std::hex << a.getOffset();
    else a.printRaw(out);
  }
  else if (cmd == "rl_insert") {
    AddrSpace *sp = spc(s); uintb first = num(s); uintb last = num(s);
    rangelist.insertRange(sp,first,last); out << rangelist.numRanges();
  }
  else if (cmd == "rl_remove") {
    AddrSpace *sp = spc(s); uintb first = num(s); uintb last = num(s);
    rangelist.removeRange(sp,first,last); out << rangelist.numRanges();
  }
  else if (cmd == "rl_print") {
    std::ostringstream t;
    rangelist.printBounds(t);
    out << tohex(t.str());
  }
  else if (cmd == "rl_query") {
    Address a = addr(s); uintb sz = num(s);
    out << rangelist.inRange(a,sz) << ' ' << std::hex << rangelist.longestFit(a,sz) << ' ';
    const Range *r = rangelist.getRange(a.getSpace(),a.getOffset());
    if (r == (const Range *)0) out << "none"; else out << r->getFirst() << '-' << r->getLast();
    out << ' ';
    r = rangelist.getNearestRange(a.getSpace(),a.getOffset());
    if (r == (const Range *)0) out << "none"; else out << r->getFirst() << '-' << r->getLast();
    out << ' ';
    r = rangelist.getLastSignedRange(a.getSpace());
    if (r == (const Range *)0) out << "none"; else out << r->getFirst() << '-' << r->getLast();
    out << ' ' << rangelist.inRange(Range(a.getSpace(),a.getOffset(),a.getOffset()+sz));
  }
  else if (cmd == "rl_encode") {
    std::ostringstream xs;
    XmlEncode xenc(xs);
    rangelist.encode(xenc);
    out << tohex(xs.str());
  }
  else if (cmd == "rl_clear") {
    rangelist.clear(); out << "ok";
  }
  else if (cmd == "helper") {
    uintb val = num(s); int4 a = inum(s); int4 b = inum(s);
    out << std::hex << calc_mask(a) << ' ' << calc_int_min(a) << ' ' << pcode_right(val,a) << ' ' << pcode_left(val,a)
	<< ' ' << minimalmask(val) << ' ' << (uintb)sign_extend((intb)val,a) << ' ' << (uintb)zero_extend((intb)val,a)
	<< ' ' << signbit_negative(val,a) << ' ' << uintb_negate(val,a) << ' ' << sign_extend(val,a,b)
	<< ' ' << extend_signbit(val,a,b) << ' ' << byte_swap(val,a) << ' ' << std::dec << leastsigbit_set(val)
	<< ' ' << mostsigbit_set(val) << ' ' << popcount(val) << ' ' << count_leading_zeros(val) << ' ' << std::hex
	<< coveringmask(val) << ' ' << std::dec << bit_transitions(val,a);
    intb swapped = (intb)val;
    byte_swap(swapped,a);
    out << ' ' << std::hex << (uintb)swapped;
  }
  else if (cmd == "istream") {
    string type = word(s); string base = word(s); string text = unhex(word(s));
    std::istringstream in(text);
    if (base == "auto") in.unsetf(std::ios::dec | std::ios::hex | std::ios::oct);
    else if (base == "hex") in >> std::hex;
    else if (base == "dec") in >> std::dec;
    else in >> std::oct;
    if (type == "u64") { uintb v = 7; in >> v; out << std::hex << v; }
    else if (type == "i64") { intb v = 7; in >> v; out << std::hex << (uintb)v; }
    else if (type == "u32") { uint4 v = 7; in >> v; out << std::hex << v; }
    else { int4 v = 7; in >> v; out << std::hex << (uint4)v; }
  }
  else if (cmd == "strtoul") {
    string text = unhex(word(s));
    char *end;
    uintb v = strtoul(text.c_str(),&end,0);
    out << std::hex << v << std::dec << ' ' << (end - text.c_str());
  }
  else if (cmd == "fhost") {
    int4 size = inum(s); uintb enc = num(s);
    FloatFormat ff(size);
    FloatFormat::floatclass tp;
    double v = ff.getHostFloat(enc,&tp);
    out << std::hex << doubleToBits(v) << std::dec << ' ' << tp << ' ' << ff.getClass(enc) << ' ' << std::hex
	<< ff.getEncoding(v);
  }
  else if (cmd == "fenc") {
    int4 size = inum(s); double v = bitsToDouble(num(s));
    FloatFormat ff(size);
    out << std::hex << ff.getEncoding(v);
  }
  else if (cmd == "fprint") {
    int4 size = inum(s); double v = bitsToDouble(num(s));
    FloatFormat ff(size);
    out << ff.printDecimal(v,false) << ' ' << ff.printDecimal(v,true);
  }
  else if (cmd == "fop") {
    int4 size = inum(s); uintb a = num(s); uintb b = num(s);
    FloatFormat ff(size);
    out << std::hex << ff.opEqual(a,b) << ff.opNotEqual(a,b) << ff.opLess(a,b) << ff.opLessEqual(a,b) << ff.opNan(a)
	<< ' ' << ff.opAdd(a,b) << ' ' << ff.opSub(a,b) << ' ' << ff.opMult(a,b) << ' ' << ff.opDiv(a,b) << ' '
	<< ff.opNeg(a) << ' ' << ff.opAbs(a) << ' ' << ff.opSqrt(a) << ' ' << ff.opCeil(a) << ' ' << ff.opFloor(a)
	<< ' ' << ff.opRound(a) << ' ' << ff.opTrunc(a,1) << ' ' << ff.opTrunc(a,2) << ' ' << ff.opTrunc(a,4) << ' '
	<< ff.opTrunc(a,8) << ' ' << ff.opInt2Float(a,1) << ' ' << ff.opInt2Float(a,2) << ' ' << ff.opInt2Float(a,4)
	<< ' ' << ff.opInt2Float(a,8);
    FloatFormat f4(4), f8(8);
    out << ' ' << ff.opFloat2Float(a,f4) << ' ' << ff.opFloat2Float(a,f8);
  }
  else if (cmd == "ctx_register") {
    string nm = word(s); int4 sb = inum(s); int4 eb = inum(s);
    try { context.registerVariable(nm,sb,eb); out << context.getContextSize(); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "ctx_default") {
    string nm = word(s); uintm v = (uintm)num(s);
    try { context.setVariableDefault(nm,v); out << std::hex << ((ContextDatabase &)context).getDefaultValue(nm); } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "ctx_setvar") {
    string nm = word(s); Address a = addr(s); uintm v = (uintm)num(s);
    try { context.setVariable(nm,a,v); out << "ok"; } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "ctx_region") {
    string nm = word(s); Address a = addr(s); Address b = addr(s); uintm v = (uintm)num(s);
    try { context.setVariableRegion(nm,a,b,v); out << "ok"; } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "ctx_changepoint") {
    Address a = addr(s); int4 w = inum(s); uintm m = (uintm)num(s); uintm v = (uintm)num(s);
    context.setContextChangePoint(a,w,m,v); out << "ok";
  }
  else if (cmd == "ctx_get") {
    string nm = word(s); Address a = addr(s);
    try {
      out << std::hex << ((ContextDatabase &)context).getVariable(nm,a) << ' ';
      uintb first,last;
      const uintm *blob = context.getContext(a,first,last);
      out << first << ' ' << last;
      for(int4 i=0;i<context.getContextSize();++i) out << ' ' << blob[i];
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
  }
  else if (cmd == "ctx_tracked") {
    Address a = addr(s); Address b = addr(s);
    lastSet = &context.createSet(a,b); out << "ok";
  }
  else if (cmd == "ctx_trackadd") {
    AddrSpace *sp = spc(s); uintb off = num(s); int4 sz = inum(s); uintb v = num(s);
    lastSet->emplace_back();
    lastSet->back().loc.space = sp; lastSet->back().loc.offset = off; lastSet->back().loc.size = sz; lastSet->back().val = v;
    out << lastSet->size();
  }
  else if (cmd == "ctx_trackval") {
    VarnodeData vn; vn.space = spc(s); vn.offset = num(s); vn.size = inum(s); Address p = addr(s);
    out << std::hex << context.getTrackedValue(vn,p);
  }
  else if (cmd == "ctx_encode") {
    std::ostringstream xs;
    XmlEncode xenc(xs);
    context.encode(xenc);
    out << tohex(xs.str());
  }
  else if (cmd == "mcodec") {
    vector<AttrSpec> specs = parseSpec(unhex(word(s)));
    string reads = unhex(word(s));
    std::ostringstream xs;
    XmlEncode xenc(xs);
    encodeSpec(xenc,specs,&trans);
    std::ostringstream ps;
    PackedEncode penc(ps);
    encodeSpec(penc,specs,&trans);
    XmlDecode xdec(&trans);
    PackedDecode pdec(&trans);
    out << tohex(xs.str()) << ' ' << tohex(ps.str()) << ' ' << decodeSpec(xdec,xs.str(),reads,specs) << ' '
	<< decodeSpec(pdec,ps.str(),reads,specs);
  }
  else if (cmd == "nested") {
    int4 depth = inum(s);
    std::ostringstream xs;
    XmlEncode xenc(xs);
    for(int4 i=0;i<depth;++i) { xenc.openElement(ELEM_DATA); if (i % 3 == 0) xenc.writeBool(ATTRIB_ALIGN,true); }
    xenc.writeString(ATTRIB_CONTENT,"x<y");
    for(int4 i=0;i<depth;++i) { xenc.closeElement(ELEM_DATA); if (i % 2 == 0) { xenc.openElement(ELEM_VAL); xenc.writeUnsignedInteger(ATTRIB_CONTENT,i); xenc.closeElement(ELEM_VAL); } }
    out << tohex(xs.str());
  }
  else if (cmd == "rangedecode") {
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      XmlDecode dec(&trans);
      dec.ingestStream(in);
      Range rng;
      rng.decode(dec);
      std::ostringstream t;
      rng.printBounds(t);
      out << t.str();
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "rangeprops") {
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      XmlDecode dec(&trans);
      dec.ingestStream(in);
      RangeProperties props;
      props.decode(dec);
      Range rng(props,&trans);
      std::ostringstream t;
      rng.printBounds(t);
      out << t.str();
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "rldecode") {
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      XmlDecode dec(&trans);
      dec.ingestStream(in);
      RangeList rl;
      rl.decode(dec);
      std::ostringstream t;
      rl.printBounds(t);
      out << tohex(t.str());
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "pcodeop") {
    Address a = addr(s);
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      XmlDecode dec(&trans);
      dec.ingestStream(in);
      PrintEmit emit;
      emit.decodeOp(a,dec);
      out << emit.out.str();
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "merge") {
    int4 count = inum(s);
    vector<VarnodeData> seq(count);
    for(int4 i=0;i<count;++i) { seq[i].space = spc(s); seq[i].offset = num(s); seq[i].size = inum(s); }
    JoinRecord::mergeSequence(seq,&trans);
    for(int4 i=0;i<seq.size();++i) { seq[i].getAddr().printRaw(out); out << ':' << std::dec << seq[i].size << ' '; }
  }
  else if (cmd == "resolve") {
    AddrSpace *sp = spc(s); uintb val = num(s); int4 sz = inum(s);
    uintb full = 0x77;
    Address r = trans.resolveConstant(sp,val,sz,Address(),full);
    r.printRaw(out); out << ' ' << std::hex << full;
  }
  else if (cmd == "cache_get") {
    Address a = addr(s);
    uintm buf[4] = { 0x55, 0x55, 0x55, 0x55 };
    cache->getContext(a,buf);
    out << std::hex << buf[0] << ' ' << buf[1] << ' ' << buf[2] << ' ' << buf[3];
  }
  else if (cmd == "cache_set") {
    Address a = addr(s); int4 w = inum(s); uintm m = (uintm)num(s); uintm v = (uintm)num(s);
    cache->setContext(a,w,m,v); out << "ok";
  }
  else if (cmd == "cache_region") {
    Address a = addr(s); Address b = addr(s); int4 w = inum(s); uintm m = (uintm)num(s); uintm v = (uintm)num(s);
    cache->setContext(a,b,w,m,v); out << "ok";
  }
  else if (cmd == "cache_allow") {
    cache->allowSet(inum(s) != 0); out << "ok";
  }
  else if (cmd == "ctx_spec") {
    string data = unhex(word(s));
    try {
      std::istringstream in(data);
      XmlDecode dec(&trans);
      dec.ingestStream(in);
      context.decodeFromSpec(dec);
      out << "ok";
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else if (cmd == "ctx_roundtrip") {
    std::ostringstream xs;
    XmlEncode xenc(xs);
    context.encode(xenc);
    ContextInternal copy;
    copy.registerVariable("mode",0,3);
    copy.registerVariable("flag",4,4);
    copy.registerVariable("big",8,23);
    copy.registerVariable("word2",32,40);
    copy.registerVariable("top",60,63);
    try {
      if (xs.str().size() != 0) {
        std::istringstream in(xs.str());
        XmlDecode dec(&trans);
        dec.ingestStream(in);
        copy.decode(dec);
      }
      std::ostringstream ys;
      XmlEncode yenc(ys);
      copy.encode(yenc);
      out << tohex(ys.str());
    } catch(LowlevelError &err) { out << "ERROR " << err.explain; }
    catch(DecoderError &err) { out << "DERROR " << err.explain; }
  }
  else {
    out << "UNKNOWN " << cmd;
  }
  return out.str();
}

int main(int argc,char **argv)
{
  AttributeId::initialize();
  ElementId::initialize();
  Probe probe;
  string line;
  while(std::getline(std::cin,line)) {
    std::istringstream s(line);
    string cmd;
    s >> cmd;
    string res;
    try { res = probe.run(cmd,s); }
    catch(LowlevelError &err) { res = "UNCAUGHT " + err.explain; }
    catch(DecoderError &err) { res = "UNCAUGHT_DECODER " + err.explain; }
    std::cout << res << '\n';
  }
  return 0;
}
