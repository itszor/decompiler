typedef struct {
  int x;
  int y;
} mystruct;

mystruct __attribute__((noinline))
foo (int c, int d)
{
  mystruct tmp;
  tmp.x = c;
  tmp.y = d;
  return tmp;
}

mystruct *glob;

int main (int argc, char *argv[])
{
  mystruct q;
  glob = &q;
  q = foo (4, 5);
  return q.x + q.y - 9;
}
