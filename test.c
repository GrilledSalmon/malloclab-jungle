#include <stdio.h>

static int hi = 124;

#define HII(a) (a)*(hi) + (hi)
#define CLASS_SIZE 21
#define WSIZE 4

static int get_class(int size) {
    size_t class_num = 3;
    while (size + WSIZE > (1<<class_num)) {
        class_num++;
    }

    if (class_num >= CLASS_SIZE) { // 나중에 에러 안 뜨면 지워주기
        printf("ERROR -- 너무 큰 사이즈가 들어와 클래스에 할당할 수 없습니다.\n");
        return NULL;
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