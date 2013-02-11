(* Functional Boolean sets, implemented using random-access lists of bit
   buckets.
   We assume arithmetic is faster than storage, hence ints are used to store
   bit sets.  This means 31 bits per bucket on a 32-bit host, so we have to
   use div/mod rather than bit masking & shifting to get at elements.  *)

let bsize = Sys.word_size - 1

(* Could also add a one-entry cache, which might speed up sequential
   accesses.  *)
type t = {
  set : int Ranlist.t;
  size : int;
}

exception Subscript

let num_buckets bits =
  (bits + bsize - 1) / bsize

let make bits =
  { set = Ranlist.make (num_buckets bits) 0; size = bits }

let empty = make 0

let lookup set bit =
  if bit >= set.size then raise Subscript;
  let bucketno = bit / bsize
  and bitno = bit mod bsize in
  let bucket = Ranlist.lookup set.set bucketno in
  ((bucket lsr bitno) land 1) = 1

let update set bit toval =
  if bit >= set.size then raise Subscript;
  let bucketno = bit / bsize
  and bitno = bit mod bsize
  and bitval = match toval with true -> 1 | false -> 0 in
  let mask = (-1) land (lnot (1 lsl bitno))
  and bucket = Ranlist.lookup set.set bucketno in
  let bucket' = (bucket land mask) lor (bitval lsl bitno) in
  {set with set = Ranlist.update set.set bucketno bucket'}

(* Combine two bool sets. Resulting size is the smaller of the two.  *)
let combine func a b =
  {
    set = Ranlist.fold_right2
            (fun a1 b1 acc -> Ranlist.cons (func a1 b1) acc)
            a.set b.set
            Ranlist.empty;
    size = min a.size b.size
  }

let union a b = combine (lor) a b

let intersection a b = combine (land) a b

let difference a b = combine (fun a b -> a land (lnot b)) a b

let fold_right func set base =
  let _, res = Ranlist.fold_right
    (fun elem (startbit, acc) ->
      let accr = ref acc in
      for bit = 0 to (bsize - 1) do
        if elem land (1 lsl bit) != 0 then
          accr := func (startbit + bit) !accr
      done;
      (startbit + bsize, !accr))
    set
    (0, base)
  in
    res

let fold_left func base set =
  let _, res = Ranlist.fold_left
    (fun (startbit, acc) elem ->
      let accr = ref acc in
      for bit = 0 to bsize - 1 do
        if elem land (1 lsl bit) != 0 then
	  accr := func !accr (startbit + bit)
      done;
      (startbit + bsize, !accr))
    (0, base)
    set in
  res

let elements set =
  fold_left (fun acc enum -> enum :: acc) [] set.set

let equal a b =
  a.size = b.size
  && Ranlist.fold_right2 (fun a1 b1 acc -> acc && a1 = b1) a.set b.set true
