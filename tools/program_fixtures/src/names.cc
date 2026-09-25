namespace geometry {
struct Circle {
    int radius;
    __attribute__((noinline)) int area() const { return 3 * radius * radius; }
};

__attribute__((noinline)) int scale(int value) { return value * 2; }
__attribute__((noinline)) int scale(int value, int factor) { return value * factor; }
}

int main(int argc, char **argv) {
    geometry::Circle circle{argc};
    return circle.area() + geometry::scale(argc) + geometry::scale(argc, 5);
}
