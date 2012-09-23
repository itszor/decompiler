int foo(unsigned short a, unsigned short b)
{
  return a * b;
}

int foo2(unsigned short a, unsigned short b)
{
  return (unsigned)a * (unsigned)b;
}
