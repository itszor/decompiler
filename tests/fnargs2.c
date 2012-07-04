void __attribute__((noinline)) bar (int a, int b, int c, int d, long long int e)
{
  __asm__ __volatile__ ("");
}

void main (int argc, char *argv[])
{
  long long x = 0x12345678abcdef90ll;
  bar (1, 2, 3, 4, x);
}
