#ifndef MARSAGLIA_H
#define MARSAGLIA_H

#include "basic.h"

uint32_t get_random(void);
void get_random_gen_state(uint32_t* w, uint32_t* z);
void set_random_gen_state(uint32_t w, uint32_t z);

#endif
