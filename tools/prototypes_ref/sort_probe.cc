#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <vector>

struct Item {
  uint32_t key;
  uint32_t tag;
};

static uint64_t state = 0x853c49e6748fea9bULL;

static uint32_t next_value(void) {
  state = state * 6364136223846793005ULL + 1442695040888963407ULL;
  return (uint32_t)(state >> 33);
}

static uint64_t fnv(const std::vector<Item> &items) {
  uint64_t hash = 0xcbf29ce484222325ULL;
  for (const Item &item : items) {
    hash ^= item.tag;
    hash *= 0x100000001b3ULL;
  }
  return hash;
}

static void emit(int size, uint32_t range, const std::vector<Item> &items) {
  std::vector<Item> sorted = items;
  std::sort(sorted.begin(), sorted.end(), [](const Item &a, const Item &b) { return a.key < b.key; });
  std::vector<Item> heaped = items;
  std::partial_sort(heaped.begin(), heaped.end(), heaped.end(),
                    [](const Item &a, const Item &b) { return a.key < b.key; });
  printf("%d %u %016llx %016llx\n", size, range, (unsigned long long)fnv(sorted),
         (unsigned long long)fnv(heaped));
}

int main(void) {
  const int sizes[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,24,31,32,33,
                       40,47,48,63,64,65,100,127,128,129,200,255,256,257,500,1000,2048};
  const uint32_t ranges[] = {1,2,3,7,100,1000000};
  for (int size : sizes) {
    for (uint32_t range : ranges) {
      std::vector<Item> items;
      for (int index = 0; index < size; ++index)
        items.push_back(Item{next_value() % range, (uint32_t)index});
      emit(size, range, items);
    }
  }
  for (int size : sizes) {
    std::vector<Item> items;
    for (int index = 0; index < size; ++index) {
      uint32_t key = (index % 2 == 0) ? (uint32_t)(index / 2) : (uint32_t)(size / 2 + index / 2);
      items.push_back(Item{key % 5, (uint32_t)index});
    }
    emit(size, 0, items);
  }
  return 0;
}
