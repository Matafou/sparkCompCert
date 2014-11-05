#include <stdio.h>

void G(int * arg);


int main(int argc, char ** argv)
{
  int n=4;
  G(&n);
  printf(" \n n == %d\n", n);
  return 0;
}
