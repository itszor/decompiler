int foo (const char *x)
{
  return *x;
}

int bar (char *const x)
{
  return *x;
}

int qux (char *volatile x)
{
  return *x;
}

int main (int argc, char *argv[])
{
  return foo (argv[0]);
}
