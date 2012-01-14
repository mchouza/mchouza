#include <stdio.h>
#define s char s[]
s="#if 0\nimport json;r=json.dumps\nprint'#include <stdio.h>\\n#define s char s[]\\ns=%s;\\n%s'%(r(s),s)\n\"\"\" \"\n#elif 1\n#undef s\nint main(void)\n{\n  char *t = s;\n  printf(\"#include <stdio.h>\\n#define s char s[]\\ns=\\\"\");\n  while (*t)\n  {\n    if (*t == '\\n')\n      printf(\"\\\\n\");\n    else if (*t == '\"')\n      printf(\"\\\\\\\"\");\n    else if (*t == '\\\\')\n      printf(\"\\\\\\\\\");\n    else\n      printf(\"%c\", *t);\n    t++;\n  }\n  printf(\"\\\";\\n%s\\n\", s);\n  return 0;\n}\n#elif 0\n\" \"\"\"\n#endif";
#if 0
import json;r=json.dumps
print'#include <stdio.h>\n#define s char s[]\ns=%s;\n%s'%(r(s),s)
""" "
#elif 1
#undef s
int main(void)
{
  char *t = s;
  printf("#include <stdio.h>\n#define s char s[]\ns=\"");
  while (*t)
  {
    if (*t == '\n')
      printf("\\n");
    else if (*t == '"')
      printf("\\\"");
    else if (*t == '\\')
      printf("\\\\");
    else
      printf("%c", *t);
    t++;
  }
  printf("\";\n%s\n", s);
  return 0;
}
#elif 0
" """
#endif
