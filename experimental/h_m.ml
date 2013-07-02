module U = struct
  type expr =
      Zero
    | True
    | False
    | Id of string
    | Pred of expr
    | Succ of expr
    | IsZero of expr
    | Cons of expr * expr
    | Car of expr
    | Cdr of expr
    | Nil
    | Null of expr
    | IfThenElse of expr * expr * expr
    | Fun of string * expr
    | Apply of expr * expr
    | LetIn of string * expr * expr
end

module T = struct
  type expr =
      Zero
    | True
    | False
    | Id of string
    | Pred of typed_expr
    | Succ of typed_expr
    | IsZero of typed_expr
    | Cons of typed_expr * typed_expr
    | Car of typed_expr
    | Cdr of typed_expr
    | Nil
    | Null of typed_expr
    | IfThenElse of typed_expr * typed_expr * typed_expr
    | Fun of string * typed_expr
    | Apply of typed_expr * typed_expr
    | LetIn of string * typed_expr * typed_expr

  and typed_expr =
      Typed of node_type * expr

  and node_type =
      Int
    | Bool
    | List of node_type
    | Arrow of node_type * node_type
    | TyVar of int
  
  let rec string_of_type = function
    Int -> "int"
  | Bool -> "bool"
  | List x -> Printf.sprintf "%s list" (string_of_type x)
  | Arrow (a, b) ->
      Printf.sprintf "%s -> %s" (string_of_type a) (string_of_type b)
  | TyVar t -> Printf.sprintf "'t%d" t
end

let rec find_subst subst_tab a =
  try
    find_subst subst_tab (Hashtbl.find subst_tab a)
  with Not_found ->
    a

let rec subst_tyvars subst = function
    T.TyVar t -> T.TyVar (find_subst subst t)
  | T.List t -> T.List (subst_tyvars subst t)
  | T.Arrow (a, b) -> T.Arrow (subst_tyvars subst a, subst_tyvars subst b)
  | x -> x

exception Type_mismatch of T.node_type * T.node_type

let imply t =
  let open T in
  let i = ref 0 in
  let new_type () =
    incr i;
    T.TyVar !i in
  let ht = Hashtbl.create 10
  and subst = Hashtbl.create 10 in
  let rec occurs tyvar = function
    Int | Bool -> false
  | List t -> occurs tyvar t
  | Arrow (a, b) -> occurs tyvar a || occurs tyvar b
  | TyVar tv -> find_subst subst tv = find_subst subst tyvar
  and add_subst a b =
    let a' = find_subst subst (max a b)
    and b' = find_subst subst (min a b) in
    if a' <> b' then begin
      Hashtbl.add subst a' b';
      if Hashtbl.mem ht a' then begin
	unify (TyVar b') (Hashtbl.find ht a');
        Hashtbl.remove ht a'
      end
    end      
  and unify t1 t2 =
    (*Printf.printf "Unifying %s & %s\n" (string_of_type t1)
		    (string_of_type t2); *)
    match t1, t2 with
      TyVar a, TyVar b ->
        add_subst a b
    | TyVar a, other
    | other, TyVar a ->
        let a' = find_subst subst a in
	if occurs a' other then
	  failwith "Recursive type"
	else if Hashtbl.mem ht a' then
	  let prevtype = Hashtbl.find ht a' in
	  (* It's very important that here PREVTYPE and OTHER are not both
	     plain TyVars!  *)
	  unify prevtype other
	else
	  Hashtbl.add ht a' other
    | Int, Int
    | Bool, Bool -> ()
    | List l1, List l2 -> unify l1 l2
    | Arrow (a1, a2), Arrow (b1, b2) -> unify a1 b1; unify a2 b2
    | t1, t2 -> raise (Type_mismatch (t1, t2)) in
  let rec imply' ctx t =
    match t with
      U.Zero -> Typed (Int, Zero)
    | U.True -> Typed (Bool, True)
    | U.False -> Typed (Bool, False)
    | U.Id x -> Typed (List.assoc x ctx, Id x)
    | U.Pred a ->
	let Typed (ta, a') = imply' ctx a in
	unify ta Int;
	Typed (Int, Pred (Typed (ta, a')))
    | U.Succ a ->
	let Typed (ta, a') = imply' ctx a in
	unify ta Int;
	Typed (Int, Succ (Typed (ta, a')))
    | U.IsZero a ->
	let Typed (ta, a') = imply' ctx a in
	unify ta Int;
	Typed (Bool, IsZero (Typed (ta, a')))
    | U.Cons (a, b) ->
        let Typed (ta, a') = imply' ctx a in
	let Typed (tb, b') = imply' ctx b in
	let nt = new_type () in
	unify nt ta;
	unify (List nt) tb;
	Typed (List nt, Cons (Typed (ta, a'), Typed (tb, b')))
    | U.Car a ->
        let Typed (ta, a') = imply' ctx a in
	let nt = new_type () in
	unify ta (List nt);
	Typed (nt, Car (Typed (ta, a')))
    | U.Cdr a ->
	let Typed (ta, a') = imply' ctx a in
	let nt = new_type () in
	unify ta (List nt);
	Typed (ta, Cdr (Typed (ta, a')))
    | U.Nil ->
	let nt = new_type () in
        Typed (List nt, Nil)
    | U.Null a ->
	let Typed (ta, a') = imply' ctx a in
	let nt = new_type () in
	unify ta (List nt);
	Typed (Bool, Null (Typed (ta, a')))
    | U.IfThenElse (a, b, c) ->
	let Typed (ta, a') = imply' ctx a in
	let Typed (tb, b') = imply' ctx b in
	let Typed (tc, c') = imply' ctx c in
	unify tb tc;
	unify ta Bool;
	Typed (tb, IfThenElse (Typed (ta, a'), Typed (tb, b'), Typed (tc, c')))
    | U.Fun (x, a) ->
	let vartype = new_type () in
	let Typed (ta, a') = imply' ((x, vartype) :: ctx) a in
	let nt1 = new_type () in
        unify nt1 (Arrow (vartype, ta));
	Typed (nt1, Fun (x, Typed (ta, a')))
    | U.Apply (a, b) ->
	let Typed (ta, a') = imply' ctx a in
	let Typed (tb, b') = imply' ctx b in
	let nt1 = new_type () in
	unify ta (Arrow (tb, nt1));
	Typed (nt1, Apply (Typed (ta, a'), Typed (tb, b')))
    | U.LetIn (x, a, b) ->
	let vartype = new_type () in
	let addvar = (x, vartype) :: ctx in
        let Typed (ta, a') = imply' ctx a in
	let Typed (tb, b') = imply' addvar b in
	unify vartype ta;
	Typed (tb, LetIn (x, Typed (ta, a'), Typed (tb, b'))) in
  let typed_expr = imply' [] t in
  (*let oldht = Hashtbl.copy ht in
  Hashtbl.clear ht;
  Hashtbl.iter
    (fun tyvar typ ->
      let tyvar' = find_subst subst tyvar
      and typ' = subst_tyvars subst typ in
      unify (TyVar tyvar') typ')
    oldht;*)
  typed_expr, ht, subst

let rec rewrite_types ht subst typed_expr =
  let open T in
  let rec lookup t =
    match t with
      TyVar t1 ->
        begin try
	  lookup (Hashtbl.find ht (find_subst subst t1))
	with Not_found ->
	  TyVar (find_subst subst t1)
	end
    | List t -> List (lookup t)
    | Arrow (a, b) -> Arrow (lookup a, lookup b)
    | x -> x in
  let Typed (t1, expr) = typed_expr in
  let expr' =
    match expr with
      Zero | True | False | Id _ | Nil -> expr
    | Pred x -> Pred (rewrite_types ht subst x)
    | Succ x -> Succ (rewrite_types ht subst x)
    | IsZero x -> IsZero (rewrite_types ht subst x)
    | Cons (x, y) -> Cons (rewrite_types ht subst x, rewrite_types ht subst y)
    | Car x -> Car (rewrite_types ht subst x)
    | Cdr x -> Cdr (rewrite_types ht subst x)
    | Null x -> Null (rewrite_types ht subst x)
    | IfThenElse (a, b, c) -> IfThenElse (rewrite_types ht subst a,
					  rewrite_types ht subst b,
					  rewrite_types ht subst c)
    | Fun (x, a) -> Fun (x, rewrite_types ht subst a)
    | Apply (a, b) -> Apply (rewrite_types ht subst a, rewrite_types ht subst b)
    | LetIn (x, a, b) -> LetIn (x, rewrite_types ht subst a,
				rewrite_types ht subst b) in
  Typed (lookup t1, expr')

let doit expr =
  try
    let typed, ht, subst = imply expr in
    let out = rewrite_types ht subst typed in
    Hashtbl.iter
      (fun i t ->
	Printf.printf "Mapping for 't%d = %s\n" i (T.string_of_type t)) ht;
    Hashtbl.iter
      (fun i t ->
	Printf.printf "Substitution 't%d = 't%d\n" i t) subst;
    Some out
  with Type_mismatch (a, b) ->
    Printf.fprintf stderr "Type mismatch (%s vs %s)\n" (T.string_of_type a)
		   (T.string_of_type b);
    flush stderr;
    None

(*let _ =
  let open U in
  doit (Cons (Cons (True, Nil), Nil))*)

(*
let rec typecheck ctx (Fix (data, e)) =
  match e with
    Zero -> Fix ((data, Int), Zero)
  | True -> Fix ((data, Bool), True)
  | False -> Fix ((data, Bool), True)
  | Id x -> Fix ((data, List.assoc x ctx), Id x)
  | Pred a ->
      let Fix ((_, t1), _) as a1 = typecheck ctx a in
      Fix ((data, Int), Pred a1)
  | Succ a ->
      let Fix ((_, t1), _) as a1 = typecheck ctx a in
      Fix ((data, Int), Succ a1)
  | IsZero a ->
      let Fix ((_, t1), _) as a1 = typecheck ctx a in
      Fix ((data, Bool), IsZero a1)
  | Cons (a, b) ->
      let Fix ((_, t1), _) as e1 = typecheck ctx a in
      let Fix ((_, t2), _) as e2 = typecheck ctx b in
      Fix ((data, t2), Cons (e1, e2))
*)

(*let rec do_typing a e =
  match e with
    Zero -> H.add a e Int
  | True -> H.add a e Bool
  | False -> H.add a e Bool
  | Pred expr ->
      do_typing a expr;
      H.add a expr Int;
      H.add a e Int
  | Succ expr ->
      do_typing a expr;
      H.add a expr Int;
      H.add a e Int
  | IsZero expr ->
      do_typing a expr;
      H.add a expr Int;
      H.add a e Bool
  | Cons (hd, tl) ->
      do_typing a hd;
      do_typing a tl;
      H.add a e (TypeOf tl);
      H.add a tl (List (TypeOf hd));
  | Car expr ->
      do_typing a expr;
      H.add a e (List (TypeOf expr))
  | Cdr expr ->
      do_typing a expr;
      let alpha = new_type () in
      H.add a e (TypeOf expr);
      H.add a expr (List alpha)
  | Nil ->
      let alpha = new_type () in
      H.add a e (List alpha)
  | Null expr ->
      let alpha = new_type () in
      do_typing a expr;
      H.add a e Bool;
      H.add a expr (List alpha)
  | IfThenElse (tst, tru, fal) ->
      do_typing a tst;
      do_typing a tru;
      do_typing a fal;
      H.add a e (TypeOf tru);
      H.add a tru (TypeOf fal);
      H.add a tst Bool
  | Fun (id, expr) ->
      do_typing a expr;
      H.add a e (Arrow (TypeOf (Id id), TypeOf expr))
  | Apply (exp1, exp2) ->
      do_typing a exp1;
      do_typing a exp2;
      H.add a exp1 (Arrow (TypeOf exp2, TypeOf e))
  | LetIn (id, exp1, exp2) ->
      do_typing a exp1;
      do_typing a exp2;
      H.add a e (TypeOf exp2);
      H.add a (Id id) (TypeOf exp1)
  | Id id ->
      let alpha = new_type () in
      H.add a e alpha

exception BothTypeof

exception TypeMismatch of typ * typ

let unify t1 t2 =
  match t1, t2 with
    TyVar a, TyVar b -> TyVar a
  | TyVar _, other -> other
  | other, TyVar _ -> other
  | TypeOf a, TypeOf b -> raise BothTypeof
  | TypeOf _, other -> other
  | other, TypeOf _ -> other
  | a, b when a = b -> a
  | _, _ -> raise (TypeMismatch (t1, t2))

let imply e =
  let ht = H.create 20 in
  do_typing ht e;
  let rec unify ta tb =
    match ta, tb with
      Int, Int -> 
  H.find ht e
*)
