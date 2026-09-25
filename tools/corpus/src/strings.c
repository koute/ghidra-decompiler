#include "corpus.h"

size_t my_strlen(const char *text)
{
  const char *cursor = text;
  while (*cursor != '\0')
    cursor++;
  return (size_t)(cursor - text);
}

int my_strcmp(const char *left, const char *right)
{
  while (*left != '\0' && *left == *right) {
    left++;
    right++;
  }
  return (unsigned char)*left - (unsigned char)*right;
}

char *my_strcpy(char *dest, const char *src)
{
  char *target = dest;
  while ((*target++ = *src++) != '\0')
    ;
  return dest;
}

void reverse_string(char *text)
{
  size_t length = my_strlen(text);
  if (length == 0)
    return;
  for (size_t low = 0, high = length - 1; low < high; low++, high--) {
    char spare = text[low];
    text[low] = text[high];
    text[high] = spare;
  }
}

int count_char(const char *text, char wanted)
{
  int total = 0;
  for (; *text != '\0'; text++) {
    if (*text == wanted)
      total++;
  }
  return total;
}

int parse_decimal(const char *text)
{
  int sign = 1;
  int value = 0;
  if (*text == '-') {
    sign = -1;
    text++;
  }
  while (*text >= '0' && *text <= '9') {
    value = value * 10 + (*text - '0');
    text++;
  }
  return sign * value;
}

void to_upper(char *text)
{
  for (; *text != '\0'; text++) {
    if (*text >= 'a' && *text <= 'z')
      *text = (char)(*text - 'a' + 'A');
  }
}
