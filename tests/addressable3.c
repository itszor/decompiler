void __attribute__((noinline))
bar (int *x)
{
  *x = 0;
}

void __attribute__((noinline))
baz (float *x)
{
  *x = 0.0;
}

int main (int argc, char *argv[])
{
  {
    int x;
    bar (&x);
  }
  {
    int z;
    bar (&z);
  }
}
