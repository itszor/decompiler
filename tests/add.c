int add_int (int a, int b)
{
  return a + b;
}

short add_short (short a, short b)
{
  return a + b;
}

unsigned short add_ushort (unsigned short a, unsigned short b)
{
  return a + b;
}

unsigned add_unsigned (unsigned a, unsigned b)
{
  return a + b;
}

volatile int x;

int main (void)
{
  x = add_int (1, 2);
  x = add_short (3, 4);
  x = add_ushort (5, 6);
  x = add_unsigned (7, 8);
  return 0;
}
