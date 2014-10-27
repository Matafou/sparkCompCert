#include <stdio.h>

void proc0(int * n);


int main(int argc, char ** argv)
{
  int x = 7;
  proc0(&x);
  printf(" x = %d\n", x);
}
