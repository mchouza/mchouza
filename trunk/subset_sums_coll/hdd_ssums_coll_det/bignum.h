#ifndef BIGNUM_H
#define BIGNUM_H

#include "basic.h"

typedef struct
{
    uint32_t d0;
    uint32_t d1;
    uint32_t d2;
} bignum_t;

void bignum_clear(bignum_t* op);
void bignum_copy(bignum_t* op1, const bignum_t* op2);
void bignum_add(bignum_t* op1, const bignum_t* op2);
int bignum_cmp(const bignum_t* op1, const bignum_t* op2);
void bignum_print(bignum_t* op);
void bignum_sprint(char* buf, bignum_t* op);

#endif
