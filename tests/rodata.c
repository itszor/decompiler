#include <stdio.h>

const int data[] = {
  1, 2, 4, 8, 16, 32, 64, 128, 256, 512
};

int main (int argc, char *argv[])
{
  int i;

  for (i = 0; i < 9; i++)
    printf ("%d\n", data[i]);

  return 0;  
}
