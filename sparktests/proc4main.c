#include <stdio.h>

void proc4(int * arg);


int main(int argc, char ** argv)
{
  int n=3;
  proc4(&n);
  printf(" \n == %d", n);
  return 0;
}
