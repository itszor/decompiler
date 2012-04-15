(* A deque is represented as a forward list & a backward list.  They are
   joined together like so (f5, b5 are the list heads):
   
   ... f5 f4 f3 f2 f1 f0 : b0 b1 b2 b3 b4 b5 ...

   So, adding a value to the front of the list (analoguous to normal cons) is
   done by appending to the front list, and adding a value to the end is
   done by appending to the back list.
   
*)


type 'a t = 'a list * 'a list

let empty = [], []

let cons v deq =
  let fw, bk = deq in v::fw, bk

let snoc deq v =
  let fw, bk = deq in fw, v::bk

let rev deq =
  let fw, bk = deq in bk, fw

let append (fwa,bwa) (fwb,bwb) =
  fwa @ (List.rev bwa), bwb @ (List.rev fwb)

let to_list deq =
  let fw, bk = deq in fw @ (List.rev bk)

let of_list lis =
  lis, []

let rev_of_list lis =
  [], lis

(* Ordering is not defined!  *)
let iter func deq =
  let fw, bk = deq in
  List.iter func fw; List.iter func bk

exception Deconstruction

let rec decon deq =
  match deq with
    [], [] -> raise Deconstruction
  | f::fw, bw -> f, (fw, bw)
  | [], bw -> decon (List.rev bw, [])

let rec noced deq =
  match deq with
    [], [] -> raise Deconstruction
  | fw, b::bw -> (fw, bw), b
  | fw, [] -> noced ([], List.rev fw)

(* "Head" and "tail" functions.  *)
let hd deq =
  try
    let l, ls = decon deq in l
  with Deconstruction ->
    raise (Failure "hd")

let tl deq =
  try
    let l, ls = decon deq in ls
  with Deconstruction ->
    raise (Failure "tl")

(* "Tip" (of tail) and "mouse" functions.  *)
let tp deq =
  try
    let ls, l = noced deq in l
  with Deconstruction ->
    raise (Failure "hd")

let ms deq =
  try
    let ls, l = noced deq in ls
  with Deconstruction ->
    raise (Failure "tl")

let is_empty = function
    [], [] -> true
  | _ -> false

let map func (fw,bw) =
  List.map func fw, List.map func bw

let filter func (fw,bw) =
  List.filter func fw, List.filter func bw

let fold_right func deq base =
  let rec scan res deq =
    if is_empty deq then
      res
    else
      let ms, tp = noced deq in
      scan (func tp res) ms
  in
    scan base deq

let fold_left func base deq =
  let rec scan res deq =
    if is_empty deq then
      res
    else
      let hd, tl = decon deq in
      scan (func res hd) tl
  in
    scan base deq

let length (fw,bw) =
  List.length fw + List.length bw

let nth deq idx =
  let rec scan deq num =
    if is_empty deq then
      raise (Failure "nth")
    else
      let hd, tl = decon deq in
      if num = idx then
        hd
      else
        scan tl (succ num) in
  scan deq 0

let printdeq d =
  let foo = fold_right (fun v a -> (string_of_int v) :: a) d [] in
  print_endline (String.concat ", " foo)

(*
let _ =
  let deq = cons 5 (cons 6 (cons 7 (cons 8 empty))) in
  let deq = snoc deq 17 in
  printdeq deq;
  printdeq (rev deq)
*)
