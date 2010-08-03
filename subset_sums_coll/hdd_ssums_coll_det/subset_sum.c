#include "bignum.h"
#include "comb_sum.h"
#include "marsaglia.h"
#include "timer.h"
#include <stdio.h>
#include <stdlib.h>

int comb_sum_cmp(const void* comb1, const void* comb2)
{
    bignum_t op1, op2;
    comb_fast_sum(&op1, (const byte*)comb1);
    comb_fast_sum(&op2, (const byte*)comb2);
    return bignum_cmp(&op1, &op2);
}

void gen_random_comb(byte* comb)
{
    ((uint32_t*)comb)[0] = get_random();
    ((uint32_t*)comb)[1] = get_random();
    ((uint32_t*)comb)[2] = get_random() & ((1 << (70 - 64)) - 1);
}

int main(void)
{
    int i;
    byte* buffer;

    comb_init();
    
    buffer = malloc(1000000000);
    for (i = 0; i < 100000000; i++)
      gen_random_comb(&buffer[i * 10]);

    printf("Buffer filled.\n");

    timer_reset();

    qsort(buffer, 10000000, 10, comb_sum_cmp);

    printf("Sorted in %fs.\n", timer_elapsed());

    free(buffer);

    comb_free();

    return 0;
}
