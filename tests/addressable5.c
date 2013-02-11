int *global;

int __attribute__((noinline))
foo (int x)
{
  (*global)++;
}

int main (int argc, char* argv[])
{
  int local = 7;
  int *localptr[5];
  localptr[2] = &local;
  global = localptr[2];
  foo (13);
  return *localptr[2];
}
