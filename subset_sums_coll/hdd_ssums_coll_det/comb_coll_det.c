#include "comb_coll_det.h"
#include "comb_sum.h"
#include <string.h>

comb_coll_det_t* ccd_create(size_t log_num_elems, size_t comb_size)
{
    comb_coll_det_t* ccd;

    ccd = malloc(sizeof(comb_coll_det_t));
    
    ccd->elem_size = comb_size;
    ccd->mask = (1 << log_num_elems) - 1;
    ccd->num_elems = 1 << log_num_elems;
    ccd->table = malloc(ccd->num_elems * ccd->elem_size);

    ccd_reset(ccd);

    return ccd;
}

void ccd_reset(comb_coll_det_t* ccd)
{
    memset(ccd->table, 0xff, ccd->num_elems * ccd->elem_size);
}

coll_type_t ccd_check_for_coll(comb_coll_det_t* ccd, const byte* comb,
                               const byte** other_comb)
{
    bignum_t sum, other_sum;
    size_t index;

    comb_fast_sum(&sum, comb);
    index = sum.d0 & ccd->mask;

    while (ccd->table[index * ccd->elem_size + 9] != 0xff)
    {
        comb_fast_sum(&other_sum, &ccd->table[index * ccd->elem_size]);
        
        if (bignum_cmp(&sum, &other_sum) == 0)
        {
            *other_comb = &ccd->table[index * ccd->elem_size];
            if (!memcmp(comb, *other_comb, ccd->elem_size))
                return coll_type_ident;
            else
                return coll_type_diff;
        }

        index++;
        index &= ccd->mask;
    }

    memcpy(&ccd->table[index * ccd->elem_size], comb, ccd->elem_size);

    *other_comb = NULL;
    return coll_type_no_coll;
}

void ccd_free(comb_coll_det_t* ccd)
{
    free(ccd->table);
    free(ccd);
}
