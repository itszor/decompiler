int *global;

int __attribute__((noinline))
foo (void)
{
  return *global;
}

int main (int argc, char* argv[])
{
  int local;
  global = &local;
  return foo ();
}
