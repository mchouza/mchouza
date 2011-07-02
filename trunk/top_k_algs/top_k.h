#ifndef TOP_K_H
#define TOP_K_H

#include <stdlib.h>

#ifdef __cplusplus
#define EXTC extern "C"
#else
#define EXTC
#endif

typedef void top_k_cp_t(int *top_k, size_t k, const int *l, size_t n);
typedef int *top_k_ip_t(int *l, size_t n, size_t k);

EXTC top_k_cp_t top_k_nlogn_cp;
EXTC top_k_cp_t top_k_nlogk_cp;
EXTC top_k_cp_t top_k_n_cp;

EXTC top_k_ip_t top_k_nlogn_ip;
EXTC top_k_ip_t top_k_n_ip;
EXTC top_k_ip_t top_k_n_ipnr;

EXTC top_k_ip_t top_k_n_ip_cpp;

#endif
