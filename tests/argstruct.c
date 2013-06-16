typedef struct
{
  int x;
  int y;
  int z;
} foo;

int __attribute__((noinline))
calc (foo *w)
{
  return w->x + w->y - w->z;
}

int
main (int argc, char* argv[])
{
  foo f;
  f.x = 1;
  f.y = 2;
  f.z = 3;
  return calc (&f);
}
