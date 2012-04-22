(* Find dominators using Lengauer & Tarjan's algorithm.  "Path compression" is
   not yet done.
   
   Needs functorizing for fun & profit!  *)

open Getoption

(*
module BLKREFSET =
  sig
    type t
    type elt
    
    val empty : t
    val fold_right : (int -> 'a -> 'a) -> t -> 'a -> 'a
    val update : t -> 'a -> t
    val elements : t -> 'a list
  end
*)

module Dominator (BS : Code.BLOCKSEQ) =
  struct
    open Block

    let ancestorWithLowestSemi blk_arr v =
      let rec scan v u =
        match v.ancestor with
          None -> u
        | Some anc ->
            let u' =
              if (get_option v.semi) < (get_option u.semi) then v
              else u
            in
              scan blk_arr.(get_option v.ancestor) u'
      in
        scan v v

    let link p nblk =
      nblk.ancestor <- Some p

    (* Finds children of immediate-dominator tree (idomchild) *)
    let invertidom blk_arr =
      Array.iteri
        (fun num node ->
          match node.idom with
	    Some idom ->
	      blk_arr.(idom).idomchild <- num :: blk_arr.(idom).idomchild
	  | None -> ())
        blk_arr

    let optional_blocks_same a b =
      match a, b with
        Some a, Some b -> a = b
      | _ -> false

    (* Might not be necessary to check membership.  *)
    let list_union n ns =
      if not (List.mem n ns) then
        n :: ns
      else
        ns

    let dominators blk_arr =
      let length = Array.length blk_arr in
      for i = length - 1 downto 1 do
        let n = blk_arr.(i) in
        let p = get_option n.parent in
        let s = List.fold_left
          (fun s v ->
            let s' = if v.dfnum <= n.dfnum then v
                     else
                       let anc = ancestorWithLowestSemi blk_arr v in
                       blk_arr.(get_option anc.semi)
            in
              if s'.dfnum < s.dfnum then s' else s)
          p
          n.predecessors in
        n.semi <- Some s.dfnum;
	s.bucket <- list_union i s.bucket;
        link p.dfnum n;
        List.iter
          (fun v ->
            let y = ancestorWithLowestSemi blk_arr blk_arr.(v) in
            if optional_blocks_same y.semi blk_arr.(v).semi then
              blk_arr.(v).idom <- Some p.dfnum
            else
              blk_arr.(v).samedom <- Some y.dfnum)
          p.bucket;
        p.bucket <- []
      done;
      for i = 1 to length-1 do
       let n = blk_arr.(i) in
       match n.samedom with
         Some sd -> n.idom <- blk_arr.(sd).idom
       | None -> ()
      done;
      invertidom blk_arr

    module RS = Boolset

    let computedf blk_arr =
      let setsize = Array.length blk_arr in
      let rec scandf node =
        let df_local =
          List.fold_left
            (fun s y ->
	      match y.idom with
	        Some idom when idom == node -> s
	      | _ -> RS.update s y.dfnum true)
            (RS.make setsize)
            blk_arr.(node).successors in
        let df_up = List.fold_left
          (fun s c ->
            scandf c;
            List.fold_left
              (fun s w ->
                if not (List.mem w blk_arr.(node).idomchild) then
                  RS.update s w true
                else s)
              s
              blk_arr.(c).domfront)
          df_local
          blk_arr.(node).idomchild in
        let elnums = RS.elements df_up in
        blk_arr.(node).domfront <- elnums
      in
        scandf 0
  end
