(* Functional random-access lists.  Algorithms borrowed from Chris Okasaki,
   "Purely Functional Data Structures" ss 9.3.1, "Skew Binary Random Access
   List".
*)

type 'a tree = Leaf of 'a | Node of 'a * 'a tree * 'a tree
type 'a t = (int * 'a tree) list

let empty = []

let is_empty ls = ls=[]

let cons x = function
    (w1, t1) :: (w2, t2) :: ts' as ts ->
      if w1 = w2 then (1 + w1 + w2, Node (x, t1, t2)) :: ts'
      else (1, Leaf x) :: ts
  | ts -> (1, Leaf x) :: ts

exception BadlyFormed

let head = function
    [] -> raise (Failure "head")
  | (1, Leaf x) :: ts -> x
  | (w, Node (x, t1, t2)) :: ts -> x
  | _ -> raise BadlyFormed

let tail = function
    [] -> raise (Failure "tail")
  | (1, Leaf x) :: ts -> ts
  | (w, Node (x, t1, t2)) :: ts -> (w lsr 1, t1) :: (w lsr 1, t2) :: ts
  | _ -> raise BadlyFormed

exception Subscript

let rec lookup_tree = function
    1, 0, Leaf x -> x
  | 1, i, Leaf x -> raise Subscript
  | w, 0, Node (x, t1, t2) -> x
  | w, i, Node (x, t1, t2) ->
      if i <= w lsr 1 then lookup_tree (w lsr 1, i - 1, t1)
      else lookup_tree (w lsr 1, i - 1 - (w lsr 1), t2)
  | _ -> raise BadlyFormed

let rec update_tree = function
    1, 0, y, Leaf x -> Leaf y
  | 1, i, y, Leaf x -> raise Subscript
  | w, 0, y, Node (x, t1, t2) -> Node (y, t1, t2)
  | w, i, y, Node (x, t1, t2) ->
      if i <= w lsr 1 then Node (x, update_tree (w lsr 1, i - 1, y, t1), t2)
      else Node (x, t1, update_tree (w lsr 1, i - 1 - w lsr 1, y, t2))
  | _ -> raise BadlyFormed

let rec lookup rl i =
  match rl with
    [] -> raise Subscript
  | (w, t) :: ts ->
      if i < w then lookup_tree (w, i, t)
      else lookup ts (i - w)

let rec update rl i y =
  match rl with
    [] -> raise Subscript
  | (w, t) :: ts ->
      if i < w then (w, update_tree (w, i, y, t)) :: ts
      else (w, t) :: update ts (i - w) y

let make n v =
  let rec scan acc n =
    if n = 0 then acc else scan (cons v acc) (n - 1)
  in
    scan empty n

let fold_right func ranlist base =
  let rec scan ranlist =
    if is_empty ranlist then
      base
    else
      func (head ranlist) (scan (tail ranlist))
  in
    scan ranlist

let fold_right2 func ranlist1 ranlist2 base =
  let rec scan ranlist1 ranlist2 =
    if is_empty ranlist1 || is_empty ranlist2 then
      base
    else
      func (head ranlist1) (head ranlist2) (scan (tail ranlist1) (tail
        ranlist2))
  in
    scan ranlist1 ranlist2

let fold_left func base ranlist =
  let rec scan acc ranlist =
    if is_empty ranlist then
      acc
    else
      scan (func acc (head ranlist)) (tail ranlist)
  in
    scan base ranlist

let fold_left2 func base ranlist1 ranlist2 =
  let rec scan acc ranlist1 ranlist2 =
    if is_empty ranlist1 || is_empty ranlist2 then
      acc
    else
      scan (func acc (head ranlist1) (head ranlist2)) (tail ranlist1)
        (tail ranlist2)
  in
    scan base ranlist1 ranlist2

let of_list ls =
  List.fold_right (fun x acc -> cons x acc) ls empty

let of_list_rev ls =
  List.fold_left (fun acc x -> cons x acc) empty ls

let to_list rls =
  fold_right (fun x acc -> x::acc) rls []

let to_list_rev rls =
  fold_left (fun acc x -> x::acc) [] rls

let of_deque deq =
  Deque.fold_right (fun x acc -> cons x acc) deq empty
  
let to_deque rls =
  fold_left (fun acc x -> Deque.snoc acc x) Deque.empty rls

let iter fn ranlist =
  fold_left (fun _ b -> fn b) () ranlist

let map fn ranlist =
  fold_right (fun hd newlist -> cons (fn hd) newlist) ranlist empty

(* There's probably a quicker (i.e. log(n)?) way of doing this, perhaps?  *)
let length rls =
  fold_left (fun acc _ -> succ acc) 0 rls
