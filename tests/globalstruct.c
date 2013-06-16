typedef struct
{
  int x;
  int y;
  int z;
} foo;

foo global = {1, 2, 3};

int __attribute__((noinline))
getint (int *w)
{
  return *w;
}

int
main (int argc, char* argv[])
{
  int y = getint (&global.y);
  return global.x + y - global.z;
}
