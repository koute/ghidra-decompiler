#ifndef CORPUS_H
#define CORPUS_H

#include <stdarg.h>
#include <stddef.h>

typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
typedef unsigned char u8;

struct point {
  int x;
  int y;
};

struct rect {
  struct point origin;
  int width;
  int height;
};

struct node {
  int value;
  struct node *next;
};

struct record {
  char name[16];
  int id;
  short kind;
  char flag;
  double weight;
};

struct device_flags {
  unsigned enabled : 1;
  unsigned mode : 3;
  unsigned priority : 4;
  unsigned channel : 6;
  unsigned reserved : 18;
};

union float_bits {
  float value;
  u32 bits;
};

typedef int (*binary_op)(int, int);

void *memcpy(void *dest, const void *src, size_t count);
void *memset(void *dest, int fill, size_t count);
void *memmove(void *dest, const void *src, size_t count);
int memcmp(const void *left, const void *right, size_t count);

int sum_array(const int *values, int count);
int find_max(const int *values, int count);
void bubble_sort(int *values, int count);
int collatz_steps(u32 start);
int count_bits(u32 word);
void matrix_multiply(int result[3][3], int left[3][3], int right[3][3]);

int switch_dense(int selector, int value);
int switch_sparse(int selector);
const char *weekday_name(int day);

int point_distance2(const struct point *first, const struct point *second);
struct point make_point(int horizontal, int vertical);
int rect_area(struct rect box);
int rect_contains(const struct rect *box, struct point probe);
int list_length(const struct node *head);
int list_sum(const struct node *head);
struct node *list_reverse(struct node *head);

size_t my_strlen(const char *text);
int my_strcmp(const char *left, const char *right);
char *my_strcpy(char *dest, const char *src);
void reverse_string(char *text);
int count_char(const char *text, char wanted);
int parse_decimal(const char *text);
void to_upper(char *text);

int factorial(int depth);
int fibonacci(int index);
int gcd(int first, int second);
int ackermann(int first, int second);

double poly_eval(const double *coefficients, int degree, double input);
float average_float(const float *values, int count);
int float_to_int(double value);
double dot_product(const double *left, const double *right, int count);
u32 float_to_bits(float value);
double clamp_double(double value, double low, double high);

int sum_varargs(int count, ...);
int call_varargs(void);
int format_hex(char *buffer, const char *prefix, ...);

void set_flags(struct device_flags *flags, int mode, int priority);
int get_mode(const struct device_flags *flags);
u32 pack_flags(struct device_flags flags);

u64 mul64(u64 first, u64 second);
i64 add64(i64 first, i64 second);
u64 shift64(u64 value, int amount);
int compare64(i64 first, i64 second);
u64 fnv1a64(const u8 *data, int length);
u64 rotate_left64(u64 value, int amount);

void copy_record(struct record *dest, const struct record *src);
void clear_record(struct record *target);
int apply_op(binary_op operation, int first, int second);
int add_ints(int first, int second);
int sub_ints(int first, int second);
void swap_ptrs(int **first, int **second);
int divide_constants(int value, u32 other);
u8 crc8(const u8 *data, int length);
int global_counter_bump(int amount);

#endif
