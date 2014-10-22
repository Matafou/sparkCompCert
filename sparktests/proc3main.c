#include <stdio.h>

void proc81(int * arg);


int main(int argc, char ** argv)
{
  int n=3;
  proc81(&n);
  printf(" \n == %d", n);
  return 0;
}
