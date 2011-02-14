#define STR_TABLE_NORMAL
#include "str_table.h"
#undef STR_TABLE_NORMAL

#define STR_TABLE_STR_CONSTS
#include "str_table.h"
#undef STR_TABLE_STR_CONSTS

#define STR_TABLE_STR_OFFSETS
#include "str_table.h"
#undef STR_TABLE_STR_OFFSETS

#include <string.h>

void str_table_init(void)
{
  size_t i;
  for (i = 1; i < sizeof(_offsets) / sizeof(_offsets[0]); i++)
    _offsets[i] += _offsets[i-1];
}

void str_table_get(char* buffer, size_t buffer_size, str_id_t str_id)
{
  if (_offsets[str_id+1] - _offsets[str_id] >= buffer_size)
    return;
  memcpy(buffer, &_table[_offsets[str_id]],
         _offsets[str_id+1] - _offsets[str_id]);
  buffer[_offsets[str_id+1] - _offsets[str_id]] = '\0';
}
