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
#define private public
#include "printjava.hh"
#undef protected
#undef private
#include <iostream>
#include <sstream>

using namespace ghidra;
using std::cin;
using std::cout;

int main(void)
{
  PrintC printc((Architecture *)0,"c-language");
  PrintJava printjava((Architecture *)0,"java-language");
  string cmd;
  while(cin >> cmd) {
    if (cmd == "base") {
      uintb val;
      cin >> hex >> val;
      cout << "base " << dec << PrintLanguage::mostNaturalBase(val) << '\n';
    }
    else if (cmd == "bin") {
      uintb val;
      cin >> hex >> val;
      ostringstream s;
      PrintLanguage::formatBinary(s,val);
      cout << "bin " << s.str() << '\n';
    }
    else if (cmd == "escape") {
      int4 first, last;
      cin >> dec >> first >> last;
      cout << "escape";
      bool current = PrintLanguage::unicodeNeedsEscape(first);
      cout << ' ' << dec << first << ':' << (current ? 1 : 0);
      for(int4 cp=first+1;cp<=last;++cp) {
	bool val = PrintLanguage::unicodeNeedsEscape(cp);
	if (val != current) {
	  current = val;
	  cout << ' ' << dec << cp << ':' << (current ? 1 : 0);
	}
      }
      cout << '\n';
    }
    else if (cmd == "hexesc") {
      int4 val;
      cin >> dec >> val;
      ostringstream s;
      PrintC::printCharHexEscape(s,val);
      cout << "hexesc " << s.str() << '\n';
    }
    else if (cmd == "uc") {
      int4 val;
      cin >> dec >> val;
      ostringstream s;
      printc.printUnicode(s,val);
      cout << "uc " << s.str() << '\n';
    }
    else if (cmd == "uj") {
      int4 val;
      cin >> dec >> val;
      ostringstream s;
      PrintLanguage *language = &printjava;
      language->printUnicode(s,val);
      cout << "uj " << s.str() << '\n';
    }
  }
  return 0;
}
