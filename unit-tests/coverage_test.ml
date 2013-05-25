open Coverage

let c = create_coverage 0l 100l

let _ =
  add_range c (Range ((), 20l, 10l));
  add_range c (Range ((), 20l, 5l));
  add_range c (Range ((), 25l, 5l));
  add_range c (Range ((), 22l, 3l))
