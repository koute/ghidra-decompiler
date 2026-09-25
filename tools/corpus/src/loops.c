#include "corpus.h"

int sum_array(const int *values, int count)
{
  int total = 0;
  for (int index = 0; index < count; index++)
    total += values[index];
  return total;
}

int find_max(const int *values, int count)
{
  int best = values[0];
  for (int index = 1; index < count; index++) {
    if (values[index] > best)
      best = values[index];
  }
  return best;
}

void bubble_sort(int *values, int count)
{
  for (int outer = 0; outer < count - 1; outer++) {
    int swapped = 0;
    for (int inner = 0; inner < count - 1 - outer; inner++) {
      if (values[inner] > values[inner + 1]) {
        int spare = values[inner];
        values[inner] = values[inner + 1];
        values[inner + 1] = spare;
        swapped = 1;
      }
    }
    if (!swapped)
      break;
  }
}

int collatz_steps(u32 start)
{
  int steps = 0;
  u32 current = start;
  do {
    if (current & 1)
      current = current * 3 + 1;
    else
      current >>= 1;
    steps++;
  } while (current > 1 && steps < 1000);
  return steps;
}

int count_bits(u32 word)
{
  int total = 0;
  while (word != 0) {
    word &= word - 1;
    total++;
  }
  return total;
}

void matrix_multiply(int result[3][3], int left[3][3], int right[3][3])
{
  for (int row = 0; row < 3; row++) {
    for (int column = 0; column < 3; column++) {
      int accumulator = 0;
      for (int inner = 0; inner < 3; inner++)
        accumulator += left[row][inner] * right[inner][column];
      result[row][column] = accumulator;
    }
  }
}
