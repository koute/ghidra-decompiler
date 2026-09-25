#include "corpus.h"

int switch_dense(int selector, int value)
{
  switch (selector) {
  case 0: return value + 17;
  case 1: return value * 31 + 4;
  case 2: return value / 3;
  case 3: return value << 5;
  case 4: return gcd(value, 1234);
  case 5: return -value;
  case 6: return value ^ 0x55;
  case 7: return count_bits((u32)value);
  case 8: return value - 100;
  case 9: return factorial(value & 7);
  default: return -1;
  }
}

int switch_sparse(int selector)
{
  switch (selector) {
  case 3: return 1;
  case 100: return 2;
  case 1000: return 3;
  case 4096: return 4;
  case -50: return 5;
  case 77777: return 6;
  default: return 0;
  }
}

static const char *const day_names[] = {
  "sunday", "monday", "tuesday", "wednesday", "thursday", "friday", "saturday"
};

const char *weekday_name(int day)
{
  if (day < 0 || day > 6)
    return "invalid";
  return day_names[day];
}
