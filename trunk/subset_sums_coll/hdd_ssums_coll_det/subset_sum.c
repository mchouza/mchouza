#include "bignum.h"
#include "comb_gen.h"
#include "comb_sum.h"
#include "timer.h"
#include <stdio.h>
#include <stdlib.h>

#if 0

int comb_sum_cmp(const void* comb1, const void* comb2)
{
    bignum_t op1, op2;
    comb_fast_sum(&op1, (const byte*)comb1);
    comb_fast_sum(&op2, (const byte*)comb2);
    return bignum_cmp(&op1, &op2);
}

int main(void)
{
    int i;
    byte* buffer;

    comb_init();

    timer_reset();
    
    buffer = malloc(1000000000);
    for (i = 0; i < 10000000; i++)
      gen_random_comb(&buffer[i * 10], 70, 35);

    printf("Buffer filled in %fs.\n", timer_elapsed());

    timer_reset();

    qsort(buffer, 10000000, 10, comb_sum_cmp);

    printf("Sorted in %fs.\n", timer_elapsed());

    free(buffer);

    comb_free();

    return 0;
}

#endif
