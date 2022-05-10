#include <stdio.h>

static int hi = 124;

#define HII(a) (a)*(hi) + (hi)

int get_class(int asize) {
    int size_class = 0;
    while ((asize > (1<<size_class)) && (size_class < 13)) {
        size_class++;
    }
    return size_class;
}

int main() {
    int class;

    for (int i=1; i<17; i++) {
        printf("%d : %d\n", i, get_class(i));    
    }
    class = get_class(100000);
    printf("%d\n", class);

    printf("%d\n", HII(10));


    return 0;
}