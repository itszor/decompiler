int __attribute__((noinline))
foo (int *y, int stride)
{
  int x[100];
  int *p = &x[3];
  for (; *y != 0;)
    *p++ = *y++;
  return x[99] + x[49] + x[0];
}

int
main (int argc, char *argv[])
{
  return foo ((int*) argv, 1);
} 
