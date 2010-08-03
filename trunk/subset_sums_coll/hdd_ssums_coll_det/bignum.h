#ifndef BIGNUM_H
#define BIGNUM_H

typedef unsigned char byte;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;

typedef struct
{
    uint32_t d0;
    uint32_t d1;
    uint32_t d2;
} bignum_t;

void bignum_clear(bignum_t* op);
void bignum_copy(bignum_t* op1, const bignum_t* op2);
void bignum_add(bignum_t* op1, const bignum_t* op2);
void bignum_print(bignum_t* op);
void bignum_sprint(char* buf, bignum_t* op);

#endif
