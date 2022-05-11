#include <stdio.h>

static int hi = 124;

#define HII(a) (a)*(hi) + (hi)

static int get_class(int size) {
    size_t class_num = 0;
    while (size > (1<<class_num)) {
        class_num++;
    }
    if (class_num < 2){
        return 2; // 최소 페이로드 크기가 WSIZE(4바이트이기 때문)
    }

    return class_num;
}


int main() {
    int class;

    for (int i=1; i<34; i++) {
        printf("%d : %d\n", i, get_class(i));    
    }
    class = get_class(1000000);
    printf("%d\n", class);

    printf("%d\n", HII(10));
    

    return 0;
}