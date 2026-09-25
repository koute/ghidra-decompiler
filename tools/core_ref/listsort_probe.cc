#include <list>
#include <cstdio>
#include <cstdlib>
struct Rec { int key; int id; };
static bool lessRec(const Rec &a,const Rec &b) {
  if (a.key >= 0 && b.key >= 0) { if (a.key != b.key) return a.key < b.key; }
  else if (a.key < 0) return true;
  else if (b.key < 0) return false;
  return false;
}
int main() {
  unsigned seed = 12345;
  for (int t=0;t<200;++t) {
    seed = seed*1103515245u + 12345u;
    int n = (seed >> 16) % 40;
    std::list<Rec> l;
    printf("case");
    for (int i=0;i<n;++i) {
      seed = seed*1103515245u + 12345u;
      int k = (int)((seed >> 16) % 7) - 2;
      if (k < 0) k = -1;
      l.push_back({k,i});
      printf(" %d", k);
    }
    printf("\n");
    l.sort(lessRec);
    printf("sorted");
    for (auto &r : l) printf(" %d", r.id);
    printf("\n");
  }
}
