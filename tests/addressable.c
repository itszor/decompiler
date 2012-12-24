void
foo (void)
{
  int c, d;
  bar (&c);
}

void
foo (void)
{
  int c[2];
  bar (&c[0]);
}

typedef struct
{
  int tmp1;
  int tmp2;
} stack_layout;

void
foo (void)
{
  stack_layout foo_stack;

  bar (&foo_start.tmp1); 
}
