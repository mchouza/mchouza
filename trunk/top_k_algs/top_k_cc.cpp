#include <algorithm>

#include "top_k.h"

int *top_k_n_ip_cpp(int *l, size_t n, size_t k)
{
    std::nth_element(l, l + n - k, l + n);
    return l + n - k;
}
