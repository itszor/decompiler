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

let i = ref 0

let new_type () =
  incr i;
  T.TyVar !i

let add_type_vars ?(continue=false) f =
  if not continue then i := 0;
  let open T in
  let rec add_types ctx e =
    let newtype, e' = match e with
      U.Zero -> Int, Zero
    | U.True -> Bool, True
    | U.False -> Bool, False
    | U.Id x -> List.assoc x ctx, Id x
    | U.Pred a -> Int, Pred (add_types ctx a)
    | U.Succ a -> Int, Succ (add_types ctx a)
    | U.IsZero a -> Bool, IsZero (add_types ctx a)
    | U.Cons (a, b) -> new_type (), Cons (add_types ctx a, add_types ctx b)
    | U.Car a -> new_type (), Car (add_types ctx a)
    | U.Cdr a -> new_type (), Cdr (add_types ctx a)
    | U.Nil -> new_type (), Nil
    | U.Null a -> Bool, Null (add_types ctx a)
    | U.IfThenElse (a, b, c) ->
	new_type (), IfThenElse (add_types ctx a, add_types ctx b,
				 add_types ctx c)
    | U.Fun (x, a) ->
        let vartype = new_type () in
	let addvar = (x, vartype) :: ctx in
	new_type (), Fun (x, add_types addvar a)
    | U.Apply (a, b) -> new_type (), Apply (add_types ctx a, add_types ctx b)
    | U.LetIn (x, a, b) ->
        let vartype = new_type () in
        let addvar = (x, vartype) :: ctx in
        new_type (), LetIn (x, add_types ctx a, add_types addvar b) in
    Typed (newtype, e') in
  add_types [] f

let imply t =
  let open T in
  let ht = Hashtbl.create 10 in
  let rec occurs tyvar = function
    Int | Bool -> false
  | List t -> occurs tyvar t
  | Arrow (a, b) -> occurs tyvar a || occurs tyvar b
  | TyVar tv -> tv = tyvar in
  let rec unify t1 t2 =
    match t1, t2 with
      TyVar a, TyVar b ->
        ()
    | (TyVar a as t'), other
    | other, (TyVar a as t') ->
	if occurs a other then
	  failwith "Recursive type"
	else begin
	  if Hashtbl.mem ht a then
	    let oldtype = Hashtbl.find ht a in
	    unify oldtype other
	  else
	    Hashtbl.add ht a other
	end
    | Int, Int
    | Bool, Bool -> ()
    | List l1, List l2 -> unify l1 l2
    | Arrow (a1, a2), Arrow (b1, b2) -> unify a1 b1; unify a2 b2
    | _, _ -> failwith "Type mismatch" in
  let rec imply' t =
    match t with
      Typed (nt, Zero) -> unify nt Int
    | Typed (nt, True) -> unify nt Bool
    | Typed (nt, False) -> unify nt Bool
    | Typed (nt, Id x) -> ()
    | Typed (nt, Pred (Typed (nt1, _) as a)) ->
	imply' a;
	unify nt1 Int;
	unify nt Int
    | Typed (nt, Succ (Typed (nt1, _) as a)) ->
	imply' a;
	unify nt1 Int;
	unify nt Int
    | Typed (nt, IsZero (Typed (nt1, _) as a)) ->
	imply' a;
	unify nt1 Int;
	unify nt Bool
    | Typed (nt, Cons ((Typed (nt1, _) as a), (Typed (nt2, _) as b))) ->
        imply' a;
	imply' b;
	unify nt nt2;
	unify nt2 (List nt1)
    | Typed (nt, Car (Typed (nt1, _) as a)) ->
        imply' a;
	unify nt1 (List nt)
    | Typed (nt, Cdr (Typed (nt1, _) as a)) ->
	imply' a;
	unify nt nt1
    | Typed (nt, Nil) ->
        unify nt (List (new_type ()))
    | Typed (nt, Null (Typed (nt1, _) as a)) ->
	imply' a;
	unify nt Bool;
	unify nt1 (List (new_type ()))
    | Typed (nt, IfThenElse ((Typed (nt1, _) as a), (Typed (nt2, _) as b),
			     (Typed (nt3, _) as c))) ->
	imply' a;
	imply' b;
	imply' c;
	unify nt nt2;
	unify nt nt3;
	unify nt1 Bool
    | Typed (nt, Fun (x, (Typed (nt1, _) as a))) ->
	imply' a;
        let x_type = new_type () in
        unify nt (Arrow (x_type, nt1))
    | Typed (nt, Apply ((Typed (nt1, _) as a), (Typed (nt2, _) as b))) ->
	imply' a;
	imply' b;
	unify nt1 (Arrow (nt2, nt))
    | Typed (nt, LetIn (x, (Typed (nt1, _) as a), (Typed (nt2, _) as b))) ->
        imply' a;
	imply' b;
	unify nt nt2 in
  imply' t;
  ht

let rec rewrite_types ht typed_expr =
  let open T in
  let rec lookup t =
    match t with
      TyVar t1 ->
        begin try
	  lookup (Hashtbl.find ht t1)
	with Not_found ->
	  t
	end
    | x -> x in
  let Typed (t1, expr) = typed_expr in
  let expr' =
    match expr with
      Zero | True | False | Id _ | Nil -> expr
    | Pred x -> Pred (rewrite_types ht x)
    | Succ x -> Succ (rewrite_types ht x)
    | IsZero x -> IsZero (rewrite_types ht x)
    | Cons (x, y) -> Cons (rewrite_types ht x, rewrite_types ht y)
    | Car x -> Car (rewrite_types ht x)
    | Cdr x -> Cdr (rewrite_types ht x)
    | Null x -> Null (rewrite_types ht x)
    | IfThenElse (a, b, c) -> IfThenElse (rewrite_types ht a,
					  rewrite_types ht b,
					  rewrite_types ht c)
    | Fun (x, a) -> Fun (x, rewrite_types ht a)
    | Apply (a, b) -> Apply (rewrite_types ht a, rewrite_types ht b)
    | LetIn (x, a, b) -> LetIn (x, rewrite_types ht a, rewrite_types ht b) in
  Typed (lookup t1, expr')

let doit expr =
  let typed = add_type_vars expr in
  let ht = imply typed in
  let out = rewrite_types ht typed in
  Hashtbl.iter
    (fun i t ->
      Printf.printf "Mapping for %d = %s\n" i (T.string_of_type t)) ht;
  out
  
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
