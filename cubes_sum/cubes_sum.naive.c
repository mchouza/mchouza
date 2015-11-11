#include <stdio.h>

int main(void)
{
    for (int a = 0; a < 1000; a++)
        for (int b = 0; b < 1000; b++)
            for (int c = 0; c < 1000; c++)
                if (1000 * 1000 * a + 1000 * b + c == a * a * a + b * b * b + c * c * c)
                    printf("%03d%03d%03d\n", a, b, c);
    return 0;
}