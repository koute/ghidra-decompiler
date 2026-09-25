#include <stdio.h>

int counter = 7;
static const unsigned int table[4] = {0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00};

__attribute__((noinline)) unsigned int lookup(int index) {
    return table[index & 3];
}

int main(int argc, char **argv) {
    counter += argc;
    printf("hello %d\n", counter);
    return (int)lookup(argc);
}
