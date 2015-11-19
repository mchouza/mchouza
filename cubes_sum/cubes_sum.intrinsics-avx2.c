#include <stdint.h>
#include <stdio.h>
#include <x86intrin.h>

typedef union
{
    __m256i m;
    uint32_t u[8];
} m256u_t;

int main(void)
{
    for (int a = 0; a < 1000; a++)
    {
        for (int b = 0; b < 1000; b++)
        {
            uint32_t lhs_ab = 1000 * 1000 * a + 1000 * b;
            m256u_t lhs_ab_v = {.u = {lhs_ab, lhs_ab, lhs_ab, lhs_ab, lhs_ab, lhs_ab, lhs_ab, lhs_ab}};
            uint32_t rhs_ab = a * a * a + b * b * b;
            m256u_t rhs_ab_v = {.u = {rhs_ab, rhs_ab, rhs_ab, rhs_ab, rhs_ab, rhs_ab, rhs_ab, rhs_ab}};
            m256u_t c_v = {.u = {0, 1, 2, 3, 4, 5, 6, 7}};
            m256u_t c_inc_v = {.u = {8, 8, 8, 8, 8, 8, 8, 8}};
            m256u_t lhs_v, rhs_v, cmp_v;
            for (int c = 0; c < 1000; c += 8)
            {
                lhs_v.m = _mm256_add_epi32(lhs_ab_v.m, c_v.m);
                rhs_v.m = _mm256_mullo_epi32(c_v.m, c_v.m);
                rhs_v.m = _mm256_mullo_epi32(rhs_v.m, c_v.m);
                rhs_v.m = _mm256_add_epi32(rhs_v.m, rhs_ab_v.m);
                cmp_v.m = _mm256_cmpeq_epi32(lhs_v.m, rhs_v.m);
                if (_mm256_movemask_epi8(cmp_v.m))
                {
                    for (int i = 0; i < 8; i++)
                        if (cmp_v.u[i] != 0)
                            printf("%09u\n", lhs_v.u[i]);
                }
                c_v.m = _mm256_add_epi32(c_v.m, c_inc_v.m);
            }
        }
    }
    return 0;
}