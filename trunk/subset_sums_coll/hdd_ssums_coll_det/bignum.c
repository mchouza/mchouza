#include "bignum.h"
#include <stdio.h>

void bignum_clear(bignum_t* op)
{
    op->d0 = 0;
    op->d1 = 0;
    op->d2 = 0;
}

void bignum_copy(bignum_t* op1, const bignum_t* op2)
{
    op1->d0 = op2->d0;
    op1->d1 = op2->d1;
    op1->d2 = op2->d2;
}

void bignum_add(bignum_t* op1, const bignum_t* op2)
{
    int i;
    uint32_t accum = 0;
    for (i = 0; i < 6; i++)
    {
        accum += ((uint16_t*)op1)[i];
        accum += ((uint16_t*)op2)[i];
        ((uint16_t*)op1)[i] = (uint16_t)accum;
        accum >>= 16;
    }
}

void bignum_print(bignum_t* op)
{
    printf("0x%08x%08x%08x\n", op->d2, op->d1, op->d0);
}

void bignum_sprint(char* buf, bignum_t* op)
{
    sprintf(buf, "0x%08x%08x%08x", op->d2, op->d1, op->d0);
}
