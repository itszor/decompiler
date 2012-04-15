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

    let blk_at_dfnum blks dfnum =
      get_option (BS.lookup blks dfnum).vertex

    let ancestorWithLowestSemi blks v =
      let rec scan v u =
        match v.ancestor with
          None -> u
        | Some anc ->
            let u' =
              if (get_option v.semi).dfnum < (get_option u.semi).dfnum then v
              else u
            in
              scan (get_option v.ancestor) u'
      in
        scan v v

    let link p nblk =
      nblk.ancestor <- Some p

    (* Finds children of immediate-dominator tree (idomchild) *)
    let invertidom blks =
      BS.iter
        (fun node ->
          match node.idom with
	    Some idom -> idom.idomchild <- node :: idom.idomchild
	  | None -> ())
        blks

    let optional_blocks_same a b =
      match a, b with
        Some a, Some b -> a.self_index = b.self_index
      | _ -> false

    (* Might not be necessary to check membership.  *)
    let list_union n ns =
      if not (List.mem n ns) then
        n :: ns
      else
        ns

    let dominators blks =
      let length = BS.length blks in
      for i = length-1 downto 1 do
        let n = blk_at_dfnum blks i in
        let p = get_option n.parent in
        let s = List.fold_left
          (fun s v ->
            let s' = if v.dfnum <= n.dfnum then v
                     else
                       let anc = ancestorWithLowestSemi blks v in
                       (get_option anc.semi)
            in
              if s'.dfnum < s.dfnum then s' else s)
          p
          n.predecessors in
        n.semi <- Some s;
	s.bucket <- list_union n s.bucket;
        link p n;
        List.iter
          (fun v ->
            let y = ancestorWithLowestSemi blks v in
            if optional_blocks_same y.semi v.semi then
              v.idom <- Some p
            else
              v.samedom <- Some y)
          p.bucket;
        p.bucket <- []
      done;
      for i = 1 to length-1 do
       let n = blk_at_dfnum blks i in
       match n.samedom with
         Some sd -> n.idom <- sd.idom
       | None -> ()
      done;
      invertidom blks

    module RS = Boolset

    let computedf blks =
      let setsize = BS.length blks in
      let rec scandf node =
        let df_local =
          List.fold_left
            (fun s y ->
	      match y.idom with
	        Some idom when idom == node -> s
	      | _ -> RS.update s y.dfnum true)
            (RS.make setsize)
            node.successors in
        let df_up = List.fold_left
          (fun s c ->
            scandf c;
            List.fold_left
              (fun s w ->
                if not (List.mem w node.idomchild) then
                  RS.update s w.dfnum true
                else s)
              s
              c.domfront)
          df_local
          node.idomchild in
        let elnums = RS.elements df_up in
        node.domfront <- List.map
          (fun n -> blk_at_dfnum blks n) elnums
      in
        scandf (blk_at_dfnum blks 0)
  end
