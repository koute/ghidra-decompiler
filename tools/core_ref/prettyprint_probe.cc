#include "prettyprint.hh"
#include <iostream>
#include <sstream>
#include <vector>

using namespace ghidra;
using std::cin;
using std::cout;

static string unescape(const string &text)
{
  string result;
  for(size_t pos=0;pos<text.size();++pos) {
    if (text[pos] == '\\' && pos + 1 < text.size()) {
      pos += 1;
      if (text[pos] == 's') result += ' ';
      else if (text[pos] == 'n') result += '\n';
      else result += text[pos];
    }
    else
      result += text[pos];
  }
  return result;
}

int main(void)
{
  string line;
  EmitPrettyPrint *emit = (EmitPrettyPrint *)0;
  ostringstream *out = (ostringstream *)0;
  vector<int4> ids;
  while(getline(cin,line)) {
    istringstream s(line);
    string cmd;
    s >> cmd;
    if (emit == (EmitPrettyPrint *)0 && cmd != "C") continue;
    try {
      if (cmd == "C") {
	int4 maxline, markup, packed;
	s >> maxline >> markup >> packed;
	delete emit;
	delete out;
	ids.clear();
	emit = new EmitPrettyPrint();
	out = new ostringstream();
	emit->setOutputStream(out);
	if (markup != 0) {
	  emit->setMarkup(true);
	  emit->setPackedOutput(packed != 0);
	}
	emit->setMaxLineSize(maxline);
      }
      else if (cmd == "P") {
	int4 hl; string text;
	s >> hl >> text;
	emit->print(unescape(text),(EmitMarkup::syntax_highlight)hl);
      }
      else if (cmd == "V") {
	int4 hl; string text;
	s >> hl >> text;
	emit->tagVariable(unescape(text),(EmitMarkup::syntax_highlight)hl,(const Varnode *)0,(const PcodeOp *)0);
      }
      else if (cmd == "T") {
	int4 hl; string text;
	s >> hl >> text;
	emit->tagOp(unescape(text),(EmitMarkup::syntax_highlight)hl,(const PcodeOp *)0);
      }
      else if (cmd == "K") {
	int4 hl; uint8 value; string text;
	s >> hl >> value >> text;
	emit->tagCaseLabel(unescape(text),(EmitMarkup::syntax_highlight)hl,(const PcodeOp *)0,value);
      }
      else if (cmd == "S") {
	int4 num, bump;
	s >> num >> bump;
	emit->spaces(num,bump);
      }
      else if (cmd == "L")
	emit->tagLine();
      else if (cmd == "LI") {
	int4 indent;
	s >> indent;
	emit->tagLine(indent);
      }
      else if (cmd == "OP") {
	string text;
	s >> text;
	ids.push_back(emit->openParen(unescape(text)));
      }
      else if (cmd == "CP") {
	string text;
	s >> text;
	emit->closeParen(unescape(text),ids.back());
	ids.pop_back();
      }
      else if (cmd == "OG")
	ids.push_back(emit->openGroup());
      else if (cmd == "CG") {
	emit->closeGroup(ids.back());
	ids.pop_back();
      }
      else if (cmd == "SI")
	ids.push_back(emit->startIndent());
      else if (cmd == "EI") {
	emit->stopIndent(ids.back());
	ids.pop_back();
      }
      else if (cmd == "SC")
	ids.push_back(emit->startComment());
      else if (cmd == "EC") {
	emit->stopComment(ids.back());
	ids.pop_back();
      }
      else if (cmd == "BS") {
	ids.push_back(emit->beginStatement((const PcodeOp *)0));
      }
      else if (cmd == "ES") {
	emit->endStatement(ids.back());
	ids.pop_back();
      }
      else if (cmd == "BP") {
	ids.push_back(emit->beginFuncProto());
      }
      else if (cmd == "EP") {
	emit->endFuncProto(ids.back());
	ids.pop_back();
      }
      else if (cmd == "BD")
	ids.push_back(emit->beginDocument());
      else if (cmd == "ED") {
	emit->endDocument(ids.back());
	ids.pop_back();
      }
      else if (cmd == "BR") {
	ids.push_back(emit->beginReturnType((const Varnode *)0));
      }
      else if (cmd == "ER") {
	emit->endReturnType(ids.back());
	ids.pop_back();
      }
      else if (cmd == "OB") {
	int4 style; string text;
	s >> style >> text;
	emit->openBrace(unescape(text),(Emit::brace_style)style);
      }
      else if (cmd == "OBI") {
	int4 style; string text;
	s >> style >> text;
	ids.push_back(emit->openBraceIndent(unescape(text),(Emit::brace_style)style));
      }
      else if (cmd == "CBI") {
	string text;
	s >> text;
	emit->closeBraceIndent(unescape(text),ids.back());
	ids.pop_back();
      }
      else if (cmd == "FILL") {
	string text;
	s >> text;
	emit->setCommentFill(unescape(text));
      }
      else if (cmd == "INC") {
	int4 val;
	s >> val;
	emit->setIndentIncrement(val);
      }
      else if (cmd == "F") {
	emit->flush();
	string res = out->str();
	cout << "OUT " << res.size() << '\n';
	cout.write(res.data(),res.size());
	cout << "\nEND\n";
      }
    }
    catch(LowlevelError &err) {
      cout << "ERR " << err.explain << "\nEND\n";
      delete emit;
      emit = (EmitPrettyPrint *)0;
    }
  }
  return 0;
}
