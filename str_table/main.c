#include "str_table.h"
#include <stdio.h>

int main(void)
{
  char str_buf[256];

  str_table_init();

  str_table_get(str_buf, sizeof(str_buf), str_first);
  printf("%s\n", str_buf);

  str_table_get(str_buf, sizeof(str_buf), str_second);
  printf("%s\n", str_buf);

  return 0;
}
