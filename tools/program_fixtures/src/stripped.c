#include <stdio.h>

__attribute__((noinline)) int square(int value) {
    return value * value;
}

__attribute__((noinline)) int twice(int value) {
    return square(value) + square(value + 1);
}

int main(int argc, char **argv) {
    printf("%d\n", twice(argc));
    return 0;
}
