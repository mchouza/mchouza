#include <math.h>
#include <stdio.h>

int main(void)
{
    for (int a = 0; a < 1000; a++)
    {
        for (int b = 0; b < 1000; b++)
        {
            /* 10^6 * a + 10^3 * b + c = a^3 + b^3 + c^3
               as we know that 0 <= c < 10^3, we have
               10^6 * a + 10^3 * b <= a^3 + b^3 + c^3 <= 10^6 * a + 10^3 * b + 999
               subtracting and taking cube roots
               cuberoot(10^6 * a + 10^3 * b - a^3 - b^3) <= c <= cuberoot(10^6 * a + 10^3 * b + 999 - a^3 - b^3)
               by using properties of floor & ceil
               ceil(cuberoot(10^6 * a + 10^3 * b - a^3 - b^3)) <= c <= floor(cuberoot(10^6 * a + 10^3 * b + 999 - a^3 - b^3)) */
            int c_lo = (int)fmax(ceil(cbrt(1000 * 1000 * a + 1000 * b - a * a * a - b * b * b)), 0.0);
            int c_hi = (int)fmin(floor(cbrt(1000 * 1000 * a + 1000 * b + 999 - a * a * a - b * b * b)), 999.0);

            for (int c = c_lo; c <= c_hi; c++)
            {
                if (1000 * 1000 * a + 1000 * b + c == a * a * a + b * b * b + c * c * c)
                    printf("%03d%03d%03d\n", a, b, c);
            }
        }
    }
    return 0;
}