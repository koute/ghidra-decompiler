#include "corpus.h"

static int sample_values[8] = { 5, -3, 12, 7, 0, 99, -40, 18 };
static char text_buffer[64];

int main(void)
{
  int total = sum_array(sample_values, 8) + find_max(sample_values, 8);
  bubble_sort(sample_values, 8);
  total += collatz_steps(27) + count_bits(0xf0f0u);
  total += switch_dense(total & 15, total) + switch_sparse(total);
  total += (int)my_strlen(weekday_name(total % 7));
  struct point first = make_point(1, 2);
  struct point second = make_point(4, 6);
  total += point_distance2(&first, &second);
  struct rect box = { { 0, 0 }, 10, 20 };
  total += rect_area(box) + rect_contains(&box, second);
  struct node tail = { 3, NULL };
  struct node head = { 4, &tail };
  total += list_length(&head) + list_sum(list_reverse(&head));
  my_strcpy(text_buffer, "Hello, corpus");
  reverse_string(text_buffer);
  to_upper(text_buffer);
  total += count_char(text_buffer, 'O') + my_strcmp(text_buffer, "abc") + parse_decimal("-1234");
  total += factorial(6) + fibonacci(10) + gcd(84, 36) + ackermann(2, 3);
  double coefficients[3] = { 1.0, 2.5, -0.5 };
  float floats[4] = { 1.0f, 2.0f, 3.5f, 4.25f };
  total += float_to_int(poly_eval(coefficients, 2, 3.0)) + (int)average_float(floats, 4);
  total += float_to_int(dot_product(coefficients, coefficients, 3) + clamp_double(2.0, 0.0, 1.0));
  total += (int)float_to_bits(1.5f);
  total += call_varargs() + format_hex(text_buffer, "0x", 0xdeadbeefu);
  struct device_flags flags = { 0 };
  set_flags(&flags, 3, 5);
  total += get_mode(&flags) + (int)pack_flags(flags);
  total += (int)mul64(0x100000003ULL, 7) + (int)add64(-5, 9) + (int)shift64(0x8000000000000001ULL, 4);
  total += compare64(-1, 1) + (int)fnv1a64((const u8 *)text_buffer, 8) + (int)rotate_left64(3, 62);
  struct record source = { "sample", 7, 2, 'y', 3.25 };
  struct record target;
  copy_record(&target, &source);
  clear_record(&source);
  total += target.id + apply_op(add_ints, 3, 4) + apply_op(sub_ints, 9, 2);
  int left_value = 1;
  int right_value = 2;
  int *left = &left_value;
  int *right = &right_value;
  swap_ptrs(&left, &right);
  total += *left + divide_constants(total, 123456u) + crc8((const u8 *)text_buffer, 10);
  total += global_counter_bump(total);
  int matrix[3][3] = { { 1, 2, 3 }, { 4, 5, 6 }, { 7, 8, 9 } };
  int product[3][3];
  matrix_multiply(product, matrix, matrix);
  total += product[2][2];
  return total;
}

void _start(void)
{
  volatile int status = main();
  for (;;)
    status++;
}
