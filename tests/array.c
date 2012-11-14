void __attribute__((noinline)) foo (int *a, int *b)
{
  for (; a < b; a++)
    *a = 0;
}

int main(void)
{
  int i[99];
  foo (i, &i[98]);
  return 0;
}
