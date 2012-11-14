int foo (int x, long long y)
{
  return x + y;
}

int bar (long long x, int y)
{
  return x - y;
}

int x;
long long y;

int main (int argc, char *argv[])
{
  return foo (x, y) * bar (y, x);
}
