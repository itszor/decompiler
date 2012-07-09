typedef float (*myfnptr) (int a, int b, short c, void *d);

void __attribute__((noinline)) foo (myfnptr jack)
{
  __asm__ __volatile__ ("");
}

int main(int argc, char *argv[])
{
  foo (0);
  return 0;
}
