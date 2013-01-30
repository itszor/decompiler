int __attribute__((noinline))
foo (int a, int b, int c, int d, int e, int f, int g)
{
  return e+f+g;
}

int __attribute__((noinline))
bar (void)
{
  return foo (1, 2, 3, 4, 5, 6, 7);
}

int main(void)
{
  return bar ();
}
