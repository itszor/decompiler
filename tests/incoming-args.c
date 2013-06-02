int __attribute__((noinline))
int1 (int x)
{
  return x;
}

int __attribute__((noinline))
int5 (int dummy1, int dummy2, int dummy3, int dummy4, int x)
{
  return x;
}

typedef struct {
  int a;
  int b;
} twoelems;

int __attribute__((noinline))
str1 (twoelems q)
{
  return q.a + q.b;
}

int __attribute__((noinline))
str2 (int dummy1, twoelems q)
{
  return q.a + q.b;
}

int __attribute__((noinline))
str3 (int dummy1, int dummy2, twoelems q)
{
  return q.a + q.b;
}

int __attribute__((noinline))
str4 (int dummy1, int dummy2, int dummy3, twoelems q)
{
  return q.a + q.b;
}

int __attribute__((noinline))
str5 (int dummy1, int dummy2, int dummy3, int dummy4, twoelems q)
{
  return q.a + q.b;
}

int main (int argc, char* argv[]) { return 0; }
