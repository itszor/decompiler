int main (int argc, char* argv[])
{
  int x = argc;
  __asm__ __volatile__ ("bfc %0, #3, #5" : "=r" (x) : "r" (x));
  return x;
}
