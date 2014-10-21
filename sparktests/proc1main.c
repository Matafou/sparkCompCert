#include <stdio.h>

void proc81(int * arg, int arg2);


int main(int argc, char ** argv)
{
  int n=3, i=9;
  proc81(&n,i);
  if (n!=3) {
    printf(" n != 3  (actually %d)\n", n); return 2;
  } else {
    printf(" n == 3\n");
  }
  return 0;
}
