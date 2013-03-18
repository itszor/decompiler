void __attribute__((noinline))
bar (unsigned short *x)
{
  *x = 0;
}

void __attribute__((noinline))
baz (short *x)
{
  *x = 0;
}

int main (int argc, char *argv[])
{
  {
    unsigned short x;
    bar (&x);
  }
  {
    short z;
    baz (&z);
  }
}
