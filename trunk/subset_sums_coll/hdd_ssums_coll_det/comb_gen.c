#include "comb_gen.h"
#include "marsaglia.h"
#include <string.h>

void gen_random_comb(byte* comb_set, uint32_t n, uint32_t k)
{
    size_t j, t;
    memset(comb_set, 0, 2 * ((n - 1) / 16 + 1));
    for (j = n - k; j < n; j++)
    {
        t = get_random() % (j + 1);
        if (comb_set[t / 8] & (1 << (t % 8)))
            comb_set[j / 8] |= (1 << (j % 8));
        else
            comb_set[t / 8] |= (1 << (t % 8));
    }
}

#if 1

#include <stdio.h>

size_t count_bits(const byte* comb_set, size_t comb_set_size)
{
    size_t bit_count = 0;
    size_t i;

    for (i = 0; i < comb_set_size * 8; i++)
        bit_count += !!(comb_set[i / 8] & (1 << (i % 8)));

    return bit_count;
}

int main(void)
{
    byte comb[10];
    int i;

    for (i = 0; i < 100000; i++)
    {
        gen_random_comb(comb, 70, 35);
        if (count_bits(comb, 10) != 35)
            printf("Error!!!");
    }

    return 0;
}

#endif
