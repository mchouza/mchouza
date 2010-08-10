#ifndef COMB_COLL_DET_H
#define COMB_COLL_DET_H

#include "basic.h"
#include <stdlib.h>

typedef struct
{
    size_t num_elems;
    size_t elem_size;
    uint32_t mask;
    byte *table;
} comb_coll_det_t;

typedef enum
{
    coll_type_no_coll,
    coll_type_ident,
    coll_type_diff
} coll_type_t;

comb_coll_det_t* ccd_create(size_t log_num_elems, size_t comb_size);
void ccd_reset(comb_coll_det_t* ccd);
coll_type_t ccd_check_for_coll(comb_coll_det_t* ccd, const byte* comb,
                               const byte** other_comb);
void ccd_free(comb_coll_det_t* ccd);

#endif
