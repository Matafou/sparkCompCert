#include <stdio.h>

void proc81(int * n);


int main(int argc, char ** argv)
{
  int x = 7;
  proc81(&x);
  printf(" x = %d", x);
}
