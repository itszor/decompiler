(* Growable functional vectors.  Basically the same thing as a Ranlist, but
   renumbered so that newly-added elements have higher indices.  *)

type 'a t =
  {
    rlist : 'a Ranlist.t;
    length : int
  }

let empty =
  {
    rlist = Ranlist.empty;
    length = 0
  }

let is_empty vec = vec.length = 0

let snoc vec x =
  {
    rlist = Ranlist.cons x vec.rlist;
    length = succ vec.length
  }

(* 'tip' (last element) and 'mouse' (all but last element) functions.  *)

let tp vec =
  Ranlist.head vec.rlist

let ms vec = 
  let rl = Ranlist.tail vec.rlist in
  {
    rlist = rl;
    length = pred vec.length
  }

let noced vec =
  match vec.length with
    0 -> None
  | _ -> Some (ms vec, tp vec)

let lookup vec i =
  Ranlist.lookup vec.rlist (vec.length - i - 1)

let update vec i y =
  { vec with rlist = Ranlist.update vec.rlist (vec.length - i - 1) y }

let make num v =
  {
    rlist = Ranlist.make num v;
    length = num
  }

let fold_right func vec base =
  Ranlist.fold_left (fun a b -> func b a) base vec.rlist

let fold_left func base vec =
  Ranlist.fold_right (fun a b -> func b a) vec.rlist base

let of_list ls =
  {
    rlist = Ranlist.of_list_rev ls;
    length = List.length ls
  }

let of_list_rev ls =
  {
    rlist = Ranlist.of_list ls;
    length = List.length ls
  }

let to_list ls =
  Ranlist.to_list_rev ls.rlist

let to_list_rev ls =
  Ranlist.to_list ls.rlist

let iter fn vec = Ranlist.iter fn vec.rlist

let map fn vec =
  {
    rlist = Ranlist.map fn vec.rlist;
    length = vec.length
  }

let append a b =
  fold_left snoc b a

let rev a =
  fold_left snoc empty a

let length vec =
  vec.length

let to_ranlist vec =
  vec.rlist

let of_ranlist rl =
  {
    rlist = rl;
    length = Ranlist.length rl
  }
