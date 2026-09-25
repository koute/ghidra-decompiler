int ext(int value);

int main(int argc, char **argv) {
    return ext(argc) + ext(3);
}

#ifdef OWN_START
void _start(void) {
    main(1, 0);
    for (;;) {
    }
}
#endif
