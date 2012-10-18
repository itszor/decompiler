struct foo {
  int x;
  int y;
};

struct foo bar;

int z1, z2;

int main(void)
{
  struct foo baz;
  bar.x = z1;
  bar.y = z2;
  baz.x = z1;
  baz.y = z2;
  return bar.x + bar.y + baz.x + baz.y;
}
