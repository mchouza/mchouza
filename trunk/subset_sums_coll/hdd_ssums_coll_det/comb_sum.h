#ifndef COMB_SUM_H
#define COMB_SUM_H

#include "bignum.h"

void comb_sum(bignum_t* sum, const byte* comb_set);
void comb_fast_sum(bignum_t* sum, const byte* comb_set);

#endif
