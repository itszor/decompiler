typedef struct {
  int a;
  int b;
} foo;

int bar (foo *x)
{
  foo y = {1, 2};
  return x->a + x->b + y.a + y.b;
}

int main (int argc, char *argv[])
{
  return bar (&(foo) { 5, 6 });
}
