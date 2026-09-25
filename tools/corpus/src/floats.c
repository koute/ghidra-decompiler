#include "corpus.h"

double poly_eval(const double *coefficients, int degree, double input)
{
  double result = 0.0;
  for (int index = degree; index >= 0; index--)
    result = result * input + coefficients[index];
  return result;
}

float average_float(const float *values, int count)
{
  float total = 0.0f;
  for (int index = 0; index < count; index++)
    total += values[index];
  return count > 0 ? total / (float)count : 0.0f;
}

int float_to_int(double value)
{
  if (value < 0.0)
    return -(int)(-value + 0.5);
  return (int)(value + 0.5);
}

double dot_product(const double *left, const double *right, int count)
{
  double total = 0.0;
  for (int index = 0; index < count; index++)
    total += left[index] * right[index];
  return total;
}

u32 float_to_bits(float value)
{
  union float_bits converter;
  converter.value = value;
  return converter.bits;
}

double clamp_double(double value, double low, double high)
{
  if (value < low)
    return low;
  if (value > high)
    return high;
  return value * 1.5;
}
