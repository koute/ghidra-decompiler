#include "translate.hh"
#include "opbehavior.hh"
#include <iostream>
#include <sstream>
#include <climits>

using namespace ghidra;
using std::cout;
using std::cin;
using std::endl;

class ProbeTranslate : public Translate {
public:
  ProbeTranslate(void) { setDefaultFloatFormats(); }
  virtual void initialize(DocumentStorage &store) {}
  virtual const VarnodeData &getRegister(const string &nm) const { throw LowlevelError("no registers"); }
  virtual string getRegisterName(AddrSpace *base,uintb off,int4 size) const { return ""; }
  virtual string getExactRegisterName(AddrSpace *base,uintb off,int4 size) const { return ""; }
  virtual void getAllRegisters(map<VarnodeData,string> &reglist) const {}
  virtual void getUserOpNames(vector<string> &res) const {}
  virtual int4 instructionLength(const Address &baseaddr) const { return -1; }
  virtual int4 oneInstruction(PcodeEmit &emit,const Address &baseaddr) const { return -1; }
  virtual int4 printAssembly(AssemblyEmit &emit,const Address &baseaddr) const { return -1; }
};

static bool divisionTraps(int4 opc,int4 sizein,uintb in1,uintb in2)

{
  if (opc != CPUI_INT_SDIV && opc != CPUI_INT_SREM) return false;
  if (in2 == 0) return false;
  intb num = sign_extend((intb)in1,8*sizein-1);
  intb denom = sign_extend((intb)in2,8*sizein-1);
  return (denom == 0) || (num == LLONG_MIN && denom == -1);
}

int main(int argc,char **argv)

{
  ProbeTranslate translate;
  vector<OpBehavior *> inst;
  OpBehavior::registerInstructions(inst,&translate);
  string line;
  while(getline(cin,line)) {
    istringstream s(line);
    int4 opc,sizeout,sizein,slot;
    string mode;
    uintb in1,in2,in3;
    s >> dec >> opc >> mode >> sizeout >> sizein >> slot >> hex >> in1 >> in2 >> in3;
    OpBehavior *behave = inst[opc];
    if (behave == (OpBehavior *)0) {
      cout << "N" << endl;
      continue;
    }
    if (mode == "m") {
      const char *name = get_opname(behave->getOpcode());
      cout << "M " << (name == (const char *)0 ? "" : name) << ' ' << behave->isUnary() << ' ' << behave->isSpecial() << endl;
      continue;
    }
    if (mode == "b" && divisionTraps(opc,sizein,in1,in2)) {
      cout << "FPE" << endl;
      continue;
    }
    try {
      uintb res = 0;
      if (mode == "u")
        res = behave->evaluateUnary(sizeout,sizein,in1);
      else if (mode == "b")
        res = behave->evaluateBinary(sizeout,sizein,in1,in2);
      else if (mode == "t")
        res = behave->evaluateTernary(sizeout,sizein,in1,in2,in3);
      else if (mode == "ru")
        res = behave->recoverInputUnary(sizeout,in1,sizein);
      else
        res = behave->recoverInputBinary(slot,sizeout,in1,sizein,in2);
      cout << "R " << hex << res << dec << endl;
    }
    catch(EvaluationError &err) {
      cout << "E Evaluation " << err.explain << endl;
    }
    catch(LowlevelError &err) {
      cout << "E Lowlevel " << err.explain << endl;
    }
  }
  return 0;
}
