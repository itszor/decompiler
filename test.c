int __attribute__((noinline)) foo (int a, int b, int c, int d, int e, int f)
{
  return (a + b) * (b + c) * (c + d) * (e + f);
}

long long int bar (int a, int b)
{
  return (long long int) a * (long long int) b;
}

int __attribute__((noinline)) blah2 (int *x)
{
  return *x;
}

int
blah (int a, int b)
{
  int c = 5;

  return blah2 (&c);
}

volatile int x;

int loop (int c)
{
  int i;
  for (i = 0x12345; i < c; i++)
    x = i;
  return c;
}

int a, b, c, d, e, f;

int main(int argc, char *argv[])
{
  return foo (a, b, c, d, e, f);
}
