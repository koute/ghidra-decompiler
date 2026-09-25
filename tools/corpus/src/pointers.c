#include "corpus.h"

static int global_counter;

static const u8 crc_table[16] = {
  0x00, 0x07, 0x0e, 0x09, 0x1c, 0x1b, 0x12, 0x15,
  0x38, 0x3f, 0x36, 0x31, 0x24, 0x23, 0x2a, 0x2d
};

void copy_record(struct record *dest, const struct record *src)
{
  __builtin_memcpy(dest, src, sizeof(struct record));
  dest->id += 1;
}

void clear_record(struct record *target)
{
  __builtin_memset(target->name, 0, sizeof(target->name));
  target->id = -1;
  target->kind = 0;
  target->flag = 'x';
  target->weight = 0.0;
}

int apply_op(binary_op operation, int first, int second)
{
  return operation(first, second) * 2;
}

int add_ints(int first, int second)
{
  return first + second;
}

int sub_ints(int first, int second)
{
  return first - second;
}

void swap_ptrs(int **first, int **second)
{
  int *spare = *first;
  *first = *second;
  *second = spare;
}

int divide_constants(int value, u32 other)
{
  return value / 7 + value % 10 + (int)(other / 3) + (int)(other % 1000);
}

u8 crc8(const u8 *data, int length)
{
  u8 crc = 0;
  for (int index = 0; index < length; index++) {
    crc = (u8)((crc << 4) ^ crc_table[(crc >> 4) ^ (data[index] >> 4)]);
    crc = (u8)((crc << 4) ^ crc_table[(crc >> 4) ^ (data[index] & 0x0f)]);
  }
  return crc;
}

int global_counter_bump(int amount)
{
  global_counter += amount;
  if (global_counter > 1000)
    global_counter = 0;
  return global_counter;
}
