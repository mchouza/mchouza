#ifdef STR_TABLE_C
#define MSG( id, str ) extern char id[sizeof(str)];
#else
#define MSG( id, str ) char id[sizeof(str)] = str;
#endif

MSG(str_first, "This is the first message.")
MSG(str_second, "This is the second message.")

#undef STR_TABLE_C
