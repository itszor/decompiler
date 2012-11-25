int __attribute__((noinline)) foo (int *x, int *x2, int *x3, int *x4, int *x5)
{
  return *x + *x2 + *x3 + *x4 + *x5;
}

int main (int argc, char *argv[])
{
  int x = 0;
  return foo (&x, &x, &x, &x, &x);  
}
