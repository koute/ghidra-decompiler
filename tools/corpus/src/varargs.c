#include "corpus.h"

int sum_varargs(int count, ...)
{
  va_list arguments;
  int total = 0;
  va_start(arguments, count);
  for (int index = 0; index < count; index++)
    total += va_arg(arguments, int);
  va_end(arguments);
  return total;
}

int call_varargs(void)
{
  return sum_varargs(3, 10, 20, 30) + sum_varargs(5, 1, 2, 3, 4, 5);
}

int format_hex(char *buffer, const char *prefix, ...)
{
  va_list arguments;
  int written = 0;
  va_start(arguments, prefix);
  while (*prefix != '\0')
    buffer[written++] = *prefix++;
  u32 value = va_arg(arguments, u32);
  for (int shift = 28; shift >= 0; shift -= 4) {
    u32 digit = (value >> shift) & 0xf;
    buffer[written++] = (char)(digit < 10 ? '0' + digit : 'a' + digit - 10);
  }
  buffer[written] = '\0';
  va_end(arguments);
  return written;
}
