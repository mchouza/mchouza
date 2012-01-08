#include <stdio.h>
char s[] = "\";\nint main(void)\n{\n  printf(\"#include <stdio.h>\\nchar s[] = \\\"\");\n  char *t = s;\n  while (*t)\n  {\n    if (*t == '\\n')\n      printf(\"\\\\n\");\n    else if (*t == '\"')\n      printf(\"\\\\\\\"\");\n    else if (*t == '\\\\')\n      printf(\"\\\\\\\\\");\n    else\n      printf(\"%c\", *t);\n    t++;\n  }\n  printf(\"%s\", s);\n  return 0;\n}\n";
int main(void)
{
  printf("#include <stdio.h>\nchar s[] = \"");
  char *t = s;
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
  printf("%s", s);
  return 0;
}
