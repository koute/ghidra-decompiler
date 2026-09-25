#include "corpus.h"

void *memcpy(void *dest, const void *src, size_t count)
{
  unsigned char *target = dest;
  const unsigned char *source = src;
  while (count-- != 0)
    *target++ = *source++;
  return dest;
}

void *memset(void *dest, int fill, size_t count)
{
  unsigned char *target = dest;
  while (count-- != 0)
    *target++ = (unsigned char)fill;
  return dest;
}

void *memmove(void *dest, const void *src, size_t count)
{
  unsigned char *target = dest;
  const unsigned char *source = src;
  if (target < source) {
    while (count-- != 0)
      *target++ = *source++;
  } else {
    while (count != 0) {
      count--;
      target[count] = source[count];
    }
  }
  return dest;
}

int memcmp(const void *left, const void *right, size_t count)
{
  const unsigned char *first = left;
  const unsigned char *second = right;
  for (size_t index = 0; index < count; index++) {
    if (first[index] != second[index])
      return first[index] < second[index] ? -1 : 1;
  }
  return 0;
}

int raise(int signal_number)
{
  return signal_number;
}
