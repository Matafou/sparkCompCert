#include <stdio.h>

void proc81(int * arg, int arg2);


int main(int argc, char ** argv)
{
  int n=3;
  printf(" AVANT proc81 \n", n);
  proc81(&n,0);
  printf(" APRÈS proc81 \n", n);
  printf(" == %d\n", n);
  return 0;
}
