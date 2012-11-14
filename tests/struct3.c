typedef struct {
  int a;
  int b;
} foo;

foo z;

int bar (foo y, foo *x)
{
  return x->a + x->b + y.a + y.b + z.a + z.b;
}

foo a, b;

int main (int argc, char *argv[])
{
  a.a = 3;
  a.b = 4;
  b.a = 5;
  b.b = 6;
  return bar (a, &b);
}
