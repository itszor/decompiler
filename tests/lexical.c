extern void bar (int *, int *);

int
foo (int d)
{
  int c;

  for (c = 0; c < d; c++)
    {
      int e, f;
      bar (&e, &f);
    }
}
