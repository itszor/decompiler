typedef struct
{
  int whatever;
} innerstruct;

typedef struct
{
  struct {
    int x;
    int x2;
  } inner;
  innerstruct y;
  int z;
} foo;

foo global = {1, 2, 3};

int __attribute__((noinline))
getint (innerstruct *w)
{
  return w->whatever;
}

int
main (int argc, char* argv[])
{
  int y = getint (&global.y);
  return global.inner.x + y - global.z;
}
