#include "corpus.h"

int factorial(int depth)
{
  if (depth <= 1)
    return 1;
  return depth * factorial(depth - 1);
}

int fibonacci(int index)
{
  if (index < 2)
    return index;
  return fibonacci(index - 1) + fibonacci(index - 2);
}

int gcd(int first, int second)
{
  if (second == 0)
    return first;
  return gcd(second, first % second);
}

int ackermann(int first, int second)
{
  if (first == 0)
    return second + 1;
  if (second == 0)
    return ackermann(first - 1, 1);
  return ackermann(first - 1, ackermann(first, second - 1));
}
