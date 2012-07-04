void __attribute__((noinline)) bar (int a, int b, int c, int d, int e, int f, int *g)
{
  __asm__ __volatile__ ("");
}

void main (int argc, char *argv[])
{
  int x[2] = { 5, 6 };
  bar (1, 2, 3, 4, x[0], x[1], x);
  bar (1, 2, 3, 4, x[0], x[1], x);
}
