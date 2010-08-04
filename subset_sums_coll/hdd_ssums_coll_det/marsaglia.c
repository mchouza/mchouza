#include "bignum.h"

static uint32_t m_w = 0xacd32662;
static uint32_t m_z = 0xaee563e2;
 
uint32_t get_random(void)
{
    m_z = 36969 * (m_z & 65535) + (m_z >> 16);
    m_w = 18000 * (m_w & 65535) + (m_w >> 16);
    return (m_z << 16) + m_w;  /* 32-bit result */
}
