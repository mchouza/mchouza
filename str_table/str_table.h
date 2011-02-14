#include <stdlib.h>

#if !defined(STR_TABLE_NORMAL) && !defined(STR_TABLE_STR_CONSTS) &&\
    !defined(STR_TABLE_STR_OFFSETS)
#define STR_TABLE_NORMAL
#endif

#if defined(STR_TABLE_NORMAL)

/* defines ids */
#define MSG(id,str ) id,
typedef enum
{

#elif defined(STR_TABLE_STR_CONSTS)

/* defines string constants */
#define MSG(id, str) str
static const char _table[] =

#elif defined(STR_TABLE_STR_OFFSETS)

/* defines string offsets */
#define MSG(id, str) sizeof(str) - 1,
static size_t _offsets[] = {
  0,

#endif

MSG(str_first, "This is the first message.")
MSG(str_second, "This is the second message.")

#if defined(STR_TABLE_NORMAL)

  str_id_last
} str_id_t;

void str_table_init(void);
void str_table_get(char* buffer, size_t buffer_size, str_id_t str_id);

#elif defined(STR_TABLE_STR_CONSTS)

;

#elif defined(STR_TABLE_STR_OFFSETS)

};

#endif

#undef MSG
