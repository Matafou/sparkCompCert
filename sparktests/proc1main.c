#include <stdio.h>

void P1(int * arg, int arg2);


int main(int argc, char ** argv)
{
  int n=3, i=9;
  P1(&n,i);
  if (n!=3) {
    printf(" n != 3  (actually %d)\n", n); return 2;
  } else {
    printf(" n == 3\n");
  }
  return 0;
}
