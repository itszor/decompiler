int __attribute__((noinline))
foo (int *x, int *xend, int *other)
{
  int i = 0;
  for (; x < xend; x++)
    i += *other;
  return i; 
}

int main (int argc, char *argv[])
{
  int x[100];
  int y = 0;

  return foo (x, &x[100], &y);
}
