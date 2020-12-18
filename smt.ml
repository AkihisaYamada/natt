open Util
open Params

type ty = Nat | Int | Real | Bool | Prod of ty * ty

type name = string

class virtual ['e,'d] base =
  object (x:'b)
    val mutable base_ty = Int
    method set_base_ty ty = base_ty <- ty
    method virtual add_assertion : 'e -> unit
    method virtual add_definition : name -> ty -> 'e -> unit
    method virtual add_declaration : 'd -> unit
    method virtual add_variable : name -> ty -> unit
    method virtual new_variable : name -> ty -> 'e
    method virtual temp_variable : ty -> 'e
    method virtual refer : ty -> 'e -> 'e
    method add_variable_base v = x#add_variable v base_ty
    method refer_base e = x#refer base_ty e
    method virtual expand : 'e -> 'e
  end;;

type exp =
  | Dummy
  | EOF
  | Nil
  | EV of name
  | LI of int
  | LR of float
  | LB of bool
  | Not of exp
  | And of exp * exp
  | Or of exp * exp
  | Xor of exp * exp
  | Imp of exp * exp
  | Neg of exp
  | Add of exp * exp
  | Sub of exp * exp
  | Mul of exp * exp
  | Div of exp * exp
  | Mod of exp * exp
  | Max of exp list
  | Eq of exp * exp
  | Ge of exp * exp
  | Gt of exp * exp
  | Le of exp * exp
  | Lt of exp * exp
  | ForAll of dec list * exp
  | Exists of dec list * exp
  | Delay of ( (exp,dec) base -> exp )
  | ZeroOne of exp list
  | ES1 of exp list
  | AtMost1 of exp list
  | OD of exp list
  | Cons of exp * exp
  | Dup of ty * exp
  | Car of exp
  | Cdr of exp
  | If of exp * exp * exp * (* flag for purity *) bool
  | App of exp list
and dec =
  | Dec of name * ty
  | Def of name * ty * exp
;;

exception Inconsistent
exception Internal of string
exception Invalid_formula of string * exp
exception Response of string * exp
exception Parse_error of string


class virtual sexp_printer =
  object (x)
    inherit Io.printer
    method virtual pr_v : string -> unit
    method virtual pr_ds : dec list -> unit
    method pr_e e =
      let pr = x#puts in
      let pr_e = x#pr_e in
      let pr_i = x#put_int in
      let pr_f = x#put_float in
      let rec withpunc put punc =
        function
        | []  -> ();
        | [e] -> put e;
        | e::es -> put e; pr punc; withpunc put punc es
      in
      let rec pr_and =
        function
        | And(e1,e2) -> pr_and e1; x#endl; pr_and e2;
        | e -> pr_e e;
      in
      let rec pr_or =
        function
        | Or(e1,e2) -> pr_or e1; x#endl; pr_or e2;
        | e -> pr_e e;
      in
      let rec pr_xor =
        function
        | Xor(e1,e2) -> pr_xor e1; x#endl; pr_xor e2;
        | e -> pr_e e;
      in
      let rec pr_add =
        function
        | Add(e1,e2) -> pr_add e1; pr " "; pr_add e2;
        | e -> pr_e e;
      in
      let rec pr_mul =
        function
        | Mul(e1,e2) -> pr_mul e1; pr " "; pr_mul e2;
        | e -> pr_e e;
      in
      match e with
      | Dummy -> pr "<Dummy>"
      | EOF   -> pr "<EOF>";
      | Nil   -> pr "()";
      | EV v  -> x#pr_v v;
      | LI i  -> if i < 0 then (pr "(- "; pr_i (-i); pr ")";) else pr_i i;
      | LR r  -> if r < 0.0 then (pr "(- "; pr_f (-. r); pr ")";) else pr_f r;
      | LB b  -> pr (if b then "true" else "false");
      | Add(e1,e2) -> pr "(+ "; pr_add e1; pr " "; pr_add e2; pr ")";
      | Sub(e1,e2) -> pr "(- "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Neg e1     -> pr "(- "; pr_e e1; pr ")";
      | Mul(e1,e2)  -> pr "(* "; pr_mul e1; pr " "; pr_mul e2; pr ")";
      | Div(e1,e2)  -> pr "(/ "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Mod(e1,e2)  -> pr "(mod "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Eq(e1,e2)   -> pr "(= "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Ge(e1,e2)   -> pr "(>= "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Gt(e1,e2)   -> pr "(> "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Le(e1,e2)   -> pr "(<= "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Lt(e1,e2)   -> pr "(< "; pr_e e1; pr " "; pr_e e2; pr ")";
      | And(e1,e2)  ->
         pr "(and ";
         x#enter 5;
         pr_and e1; x#endl;
         pr_and e2;
         x#leave 5;
         pr ")";
      | Or(e1,e2)   ->
        pr "(or ";
        x#enter 4;
        pr_or e1; x#endl;
        pr_or e2;
        x#leave 4;
        pr ")";
      | Xor(e1,e2)  ->
        pr "(xor ";
        x#enter 5;
        pr_xor e1; x#endl;
        pr_xor e2;
        x#leave 5;
        pr ")";
      | Not e1    ->
        pr "(not ";
        x#enter 5;
        pr_e e1;
        x#leave 5;
        pr ")";
      | Imp(e1,e2)  ->
        pr "(=> ";
        x#enter 4;
        pr_e e1; x#endl;
        pr_e e2;
        x#leave 4;
        pr ")";
      | ForAll(ds,e)  ->
        pr "(forall (";
        x#enter 7;
        x#pr_ds ds; pr ")"; x#endl;
        pr_e e;
        pr ")";
        x#leave 7;
        x#endl;
      | Exists(ds,e)  ->
        pr "(exists (";
        x#enter 7;
        x#pr_ds ds; pr ") ";
        x#leave 7;
        pr_e e; pr ")";
        x#endl;
      | Cons(e1,e2) -> pr "(cons "; pr_e e1; pr " "; pr_e e2; pr ")";
      | Dup(_,e)    -> pr "(dup "; pr_e e; pr ")";
      | Car(e)    -> pr "(car "; pr_e e; pr ")";
      | Cdr(e)    -> pr "(cdr "; pr_e e; pr ")";
      | If(e1,e2,e3,_)  -> x#enter_inline;
                 pr "(ite "; pr_e e1; pr " "; pr_e e2; pr " "; pr_e e3; pr ")";
                 x#leave_inline;
      | Max(es)   -> pr "(max"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
      | ZeroOne(es) -> pr "(zeroone"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
      | ES1(es)   -> pr "(es1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
      | AtMost1(es) -> pr "(atmost1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
      | OD(es)    -> pr "(od"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
      | App(es)   -> pr "("; withpunc pr_e " " es; pr ")";
      | Delay f   -> pr "(delay...)";
  end;;

class sexp_printer_wrap (base : #Io.printer) = object
  inherit sexp_printer
  inherit Io.printer
  (* Tedious! Can't be done elegantly? *)
  method puts = base#puts
  method putc = base#putc
  method put_int = base#put_int
  method flush = base#flush
  method close = base#close
  method endl = base#endl
  method enter = base#enter
  method leave = base#leave
  method pr_v = base#puts
  method pr_ds = raise (No_support "SMT")
end;;

let put_exp e (pr : #Io.printer) = (new sexp_printer_wrap pr)#pr_e e

let prerr_exp e = put_exp e Io.cerr


let is_zero =
  function
  | LI 0 -> true
  | LR 0.0 -> true
  | _ -> false

let is_one =
  function
  | LI 1 -> true
  | LR 1.0 -> true
  | _ -> false

let is_simple =
  let very_simple =
    function
    | Nil
    | EV _
    | Not (EV _)
    | LI _
    | LB _
    | LR _    -> true
    | _ -> false
  in
  fun e -> very_simple e ||
  match e with
  | If(c,t,e, _) when very_simple c && very_simple t && very_simple e -> true
(*  | And(e1,e2)-> is_simple e1 && is_simple e2
  | Or(e1,e2) -> is_simple e1 && is_simple e2
*)
  | Eq(e1,e2) -> very_simple e1 && very_simple e2
  | Gt(e1,e2) -> very_simple e1 && very_simple e2
  | Ge(e1,e2) -> very_simple e1 && very_simple e2
  | _     -> false

let rec smt_not =
  function
  | LB b  -> LB (not b)
  | Not e -> e
  | Gt(e1,e2) -> Ge(e2,e1)
  | Ge(e1,e2) -> Gt(e2,e1)
  | Or(e1,e2) -> And(smt_not e1, smt_not e2)
  | And(e1,e2) -> Or(smt_not e1, smt_not e2)
  | If(c,t,e,p) -> If(c, smt_not t, smt_not e, p)
  | e   -> Not(e)

let smt_expand e f =
  if is_simple e then f e else Delay(fun context -> f (context#expand e))

let smt_let ty e f =
  if is_simple e then f e else Delay(fun context -> f (context#refer ty e))

let smt_let_base e f =
  if is_simple e then f e else Delay(fun context -> f (context#refer_base e))


let rec simplify_under e1 e2 =
  match e1, e2 with
  | LB b, _ -> if b then e2 else e1
  | And(e3,e4), _ -> e2 (*simplify_under e3 (simplify_under e4 e2)*)
  | Or _, _ -> e2
  | _, LB _
  | _, LI _
  | _, LR _ -> e2
  | _, Add(e3,e4) -> simplify_under e1 e3 +^ simplify_under e1 e4
  | _, Mul(e3,e4) -> simplify_under e1 e3 *^ simplify_under e1 e4
  | EV v1, EV v2 -> if v1 = v2 then LB true else e2
  | EV v1, Not(EV v2) -> if v1 = v2 then LB false else e2
  | Not(EV v1), EV v2 -> if v1 = v2 then LB false else e2
  | Not(EV v1), Not(EV v2) -> if v1 = v2 then LB true else e2
  | _, And(e3,e4) -> (
    let e3 = simplify_under e1 e3 in
    if e3 = LB false then e3
    else
      let e4 = simplify_under e1 e4 in
(*
      let e4 = simplify_under e3 e4 in
*)
      if e3 = LB true then e4
      else if e4 = LB false then e4
      else if e4 = LB true then e3
      else And(e3,e4)
  )
  | _, Or(e3,e4) -> (
    let e3 = simplify_under e1 e3 in
    if e3 = LB true then e3
    else
      let e4 = simplify_under e1 e4 in
(*
      let e4 = simplify_under (smt_not e3) e4 in
*)
      if e3 = LB false then e4
      else if e4 = LB false then e3
      else if e4 = LB true then e4
      else if simple_eq e3 e4 = Some true then e3
      else Or(e3,e4)
  )
  | _, If(c,t,e,p) -> (
    match simplify_under e1 c with
    | LB b -> if b then simplify_under e1 t else simplify_under e1 e
    | c ->
      (* t and e should be already simplified w.r.t. c *)
      If(c, simplify_under e1 t, simplify_under e1 e, p)
  )
  | Eq(l1,r1), Gt(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if (r2 >=^ l1) = LB true && (r1 >=^ l2) = LB true then LB false
    else l2 >^ r2
  | Eq(l1,r1), Ge(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
    else l2 >=^ r2
  | Gt(l1,r1), Eq(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true ||
       r2 >=^ l1 = LB true && r1 >=^ l2 = LB true
    then LB false
    else l2 =^ r2
  | Gt(l1,r1), Gt(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
    else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
    else l2 >^ r2
  | Gt(l1,r1), Ge(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
    else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
    else l2 >^ r2
  | Ge(l1,r1), Ge(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
    else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then l2 =^ r2
    else l2 >=^ r2
  | Ge(l1,r1), Gt(l2,r2) ->
    let l2 = simplify_under e1 l2 in
    let r2 = simplify_under e1 r2 in
    if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
    else l2 >^ r2
  | _ -> e2
and (&^) e1 e2 =
  match e1 with
  | LB b -> if b then e2 else e1
  | _ ->
    match simplify_under e1 e2 with
    | LB b -> if b then e1 else LB false
    | e2 -> And(e1,e2)
and (|^) e1 e2 =
  match e1 with
  | LB b -> if b then e1 else e2
  | _ ->
    match simplify_under (smt_not e1) e2 with
    | LB b -> if b then LB true else e1
    | e2 -> Or(e1,e2)
and (=>^) e1 e2 = smt_not e1 |^ e2
and simple_eq e1 e2 =
  match e1, e2 with
  | LB b1, LB b2 -> Some (b1 = b2)
  | LI i1, LI i2  -> Some (i1 = i2)
  | LR r1, LR r2  -> Some (r1 = r2)
  | Not e1, Not e2 -> simple_eq e1 e2
  | EV v1, EV v2 when v1 = v2 -> Some true
  | Not(EV v1), EV v2 when v1 = v2 -> Some false
  | EV v1, Not (EV v2) when v1 = v2 -> Some false
  | Nil, Nil
  | _ -> None
and (=^) e1 e2 =
  match simple_eq e1 e2 with Some b -> LB b
  | None -> (
    match e1, e2 with
    | LB b1, _ -> if b1 then e2 else smt_not e2
    | _, LB b2 -> if b2 then e1 else smt_not e1
    | LI i1, LI i2  -> LB (i1 = i2)
    | LR r1, LR r2  -> LB (r1 = r2)
    | Not e1, Not e2 -> e1 =^ e2
    | Nil, Nil -> LB true
    | EV v1, EV v2 when v1 = v2 -> LB true
    | Ge(l1,r1),Ge(l2,r2) when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true -> LB true
    | Gt(l1,r1),Gt(l2,r2) when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true -> LB true
    | Eq(l1,r1),Eq(l2,r2)
    when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true
      || simple_eq l1 r2 = Some true && simple_eq r1 l2 = Some true
    -> LB true
(*    | If(c,t,e,p), e2 -> (
      match t =^ e2 with
      | LB b -> (
        match e =^ e2 with
        | LB b' ->
          if b then if b' then LB true else c
          else if b' then smt_not c else LB false
        | e' -> if b then c |^ e' else smt_not c &^ e'
        )
      | t' -> (
        match e =^ e2 with
        | LB b' ->
          if b' then c =>^ t' else c &^ t'
        | _ -> Eq(e1, e2)
        )
      )
    | _, If(c,t,e,p) -> (
      match e1 =^ t with
      | LB b -> (
        match e1 =^ e with
        | LB b' ->
          if b then if b' then LB true else c
          else if b' then smt_not c else LB false
        | e' -> if b then c |^ e' else smt_not c &^ e'
        )
      | t' -> (
        match e1 =^ e with
        | LB b' ->
          if b' then c =>^ t' else c &^ t'
        | _ -> Eq(e1, e2)
        )
      )
*)    | _ -> Eq (e1, e2)
  )
and ( *^) e1 e2 =
  match e1, e2 with
  | LI 0, _
  | LR 0.0, _ -> e1
  | _, LI 0
  | _, LR 0.0 -> e2
  | LI 1, _
  | LR 1.0, _ -> e2
  | _, LI 1
  | _, LR 1.0 -> e1
  | LI i1, LI i2 -> LI(i1 * i2)
  | LR r1, LR r2 -> LR(r1 *. r2)
  | If(c,t,e,p), _ when is_zero t ->
    let nc = smt_not c in smt_pre_if c nc t (e *^ simplify_under nc e2)
  | If(c,t,e,p), _ when is_zero e ->
    smt_pre_if c (smt_not c) (t *^ simplify_under c e2) e
  | _, If(c,t,e,p) when is_zero t ->
    let nc = smt_not c in smt_pre_if c nc t (simplify_under nc e1 *^ e)
  | _, If(c,t,e,p) when is_zero e ->
    smt_pre_if c (smt_not c) (simplify_under c e1 *^ t) e
  | _ -> Mul(e1,e2)
and smt_pre_if c nc t e =
    match t, e with
    | LB b, _ -> if b then c |^ e else nc &^ e
    | _, LB b -> if b then c =>^ t else c &^ t
    | _ when simple_eq t e = Some true -> t
    | If(c',t',e',p), _ when simple_eq e' e = Some true -> If(c  &^ c', t', e', p)
    | If(c',t',e',p), _ when simple_eq t' e = Some true -> If(nc &^ c', t', e', p)
    | _, If(c',t',e',p) when simple_eq e' t = Some true -> If(nc &^ c', t', e', p)
    | _, If(c',t',e',p) when simple_eq t' t = Some true -> If(c  &^ c', t', e', p)
    | Nil, _
    | _, Nil
    | Cons _, _
    | _, Cons _
    | If(_,_,_,false), _
    | _, If(_,_,_,false) -> If(c,t,e,false)
    | _ -> If(c,t,e,true)
and smt_if c t e =
  match c with
  | LB b  -> if b then t else e
  | _   -> let nc = smt_not c in smt_pre_if c nc (simplify_under c t) (simplify_under nc e)
and (+^) e1 e2 =
  match e1, e2 with
  | LI 0,  _    -> e2
  | LR 0.0, _   -> e2
  | _, LI 0   -> e1
  | _, LR 0.0   -> e1
  | LI i1, LI i2  -> LI(i1 + i2)
  | LR r1, LR r2  -> LR(r1 +. r2)
  | Max es1, _  -> Max(List.map (fun e1 -> e1 +^ e2) es1)
  | _, Max es2  -> Max(List.map (fun e2 -> e1 +^ e2) es2)
  | Add(e3,e4),_  -> Add(e3, e4 +^ e2)
  | _       -> Add(e1,e2)
and (>=^) e1 e2 =
  match e1, e2 with
  | EV v1, EV v2 when v1 = v2 -> LB true
  | LI i1, LI i2 -> LB(i1 >= i2)
  | LI i1, LR r2 -> LB(float_of_int i1 >= r2)
  | LR r1, LI i2 -> LB(r1 >= float_of_int i2)
  | LR r1, LR r2 -> LB(r1 >= r2)
  | If(c,t,e,p), e2 -> (
    match t >=^ e2 with
    | LB b -> (
      match e >=^ e2 with
      | LB b' ->
        if b then if b' then LB true else c
        else if b' then smt_not c else LB false
      | e' -> if b then c |^ e' else smt_not c &^ e'
      )
    | t' -> (
      match e >=^ e2 with
      | LB b' ->
        if b' then c =>^ t' else c &^ t'
      | _ -> Ge(e1, e2)
      )
    )
  | _, If(c,t,e,p) -> (
    match e1 >=^ t with
    | LB b -> (
      match e1 >=^ e with
      | LB b' ->
        if b then if b' then LB true else c
        else if b' then smt_not c else LB false
      | e' -> if b then c |^ e' else smt_not c &^ e'
      )
    | t' -> (
      match e1 >=^ e with
      | LB b' ->
        if b' then c =>^ t' else c &^ t'
      | _ -> Ge(e1, e2)
      )
    )
  | _ -> Ge(e1, e2)
and (>^) e1 e2 =
  match e1, e2 with
  | LI 0, _ -> LB false
  | EV v1, EV v2 when v1 = v2 -> LB false
  | LI i1, LI i2 -> LB(i1 > i2)
  | LI i1, LR r2 -> LB(float_of_int i1 > r2)
  | LR r1, LI i2 -> LB(r1 > float_of_int i2)
  | LR r1, LR r2 -> LB(r1 > r2)
  | If(c,t,e,p), _ -> (
    match t >^ e2 with
    | LB b -> (
      match e >^ e2 with
      | LB b' ->
        if b then if b' then LB true else c
        else if b' then smt_not c else LB false
      | e' -> if b then c |^ e' else smt_not c &^ e'
      )
    | t' -> (
      match e >^ e2 with
      | LB b' ->
        if b' then c =>^ t' else c &^ t'
      | _ -> Gt(e1,e2)
      )
    )
  | _, If(c,t,e,p) -> (
    match e1 >^ t with
    | LB b -> (
      match e1 >^ e with
      | LB b' ->
        if b then if b' then LB true else c
        else if b' then smt_not c else LB false
      | e' -> if b then c |^ e' else smt_not c &^ e'
      )
    | t' -> (
      match e1 >^ e with
      | LB b' ->
        if b' then c =>^ t' else c &^ t'
      | _ -> Gt(e1,e2)
      )
    )
  | _ -> Gt(e1,e2)

let (<>^) e1 e2 = smt_not (e1 =^ e2)

let (<=^) e1 e2 = e2 >=^ e1
let (<^) e1 e2 = e2 >^ e1

let (/^) e1 e2 =
  if e1 = LI 0 || e2 = LI 1 then e1
  else Div(e1,e2)

let smt_xor e1 e2 =
  match e1, e2 with
  | LB b, _ -> if b then smt_not e2 else e2
  | _, LB b -> if b then smt_not e1 else e1
  | _ ->
    match e1 =^ e2 with LB b -> LB (not b) | _ -> Xor(e1,e2)


let smt_for_all f = List.fold_left (fun ret e -> ret &^ f e) (LB true)

let smt_for_all2 f = List.fold_left2 (fun ret e1 e2 -> ret &^ f e1 e2) (LB true)

let smt_exists f = List.fold_left (fun ret e -> ret |^ f e) (LB false)

let smt_exists2 f = List.fold_left2 (fun ret e1 e2 -> ret |^ f e1 e2) (LB false)

let smt_mod e1 e2 = Mod(e1,e2)
let smt_max e1 e2 =
  match e1, e2 with
  | LI i1, LI i2  -> LI(if i1 > i2 then i1 else i2)
  | _, Max es2  -> Max(e1::es2)
  | Max es1,_   -> Max(e2::es1)
  | _,_     -> Max[e1;e2]

let smt_car =
  function
  | Cons(e,_) -> e
  | Dup(_,e) -> e
  | e -> Car e

let smt_cdr =
  function
  | Cons(_,e) -> e
  | Dup(_,e) -> e
  | e -> Cdr e

let smt_split e f =
  match e with
  | Cons(e1,e2) -> f e1 e2
  | _ -> smt_expand e (function Cons(e1,e2) -> f e1 e2 | _ -> raise (Invalid_formula ("smt_split", e)))


;;

class virtual context =

  object (x:'t)
    inherit [exp,dec] base

    method virtual private add_assertion_body : exp -> unit
    method virtual private add_declaration_body : dec -> unit

    method private branch = new subcontext

    val mutable consistent = true

    method add_assertion =
      let rec sub =
        function
        | And(e1,e2)  -> sub e1; sub e2;
        | LB true   -> ();
        | e ->
          x#add_assertion_body e;
          if e = LB false then (consistent <- false; raise Inconsistent);
      in
      fun e -> if consistent then sub (x#expand e);

    method private add_declaration d =
      if consistent then begin
        let d =
          match d with
          | Def(v,ty,e) -> Def(v,ty,x#expand e)
          | _ -> d
        in
        x#add_declaration_body d;
      end
    method add_definition v ty e =
      x#add_declaration (Def(v,ty,e))

    method add_variable v ty = x#add_declaration (Dec(v,ty))

    method new_variable v ty = x#add_variable v ty; EV v

    val mutable temp_names = 0
    method private temp_name =
      let v = "_" ^ string_of_int temp_names in
      temp_names <- temp_names + 1;
      v

    method temp_variable ty =
      x#new_variable x#temp_name ty

    method private refer_sub ty e =
      if not params.tmpvar || not consistent || is_simple e then e
      else
        match e with
          (* Impure formula will not be represented by a variable *)
        | If(c,t,e,false) ->
          If(x#refer_sub Bool c, x#refer_sub ty t, x#refer_sub ty e, false)
        | Cons(e1,e2) ->
          (match ty with
           | Prod(ty1,ty2) -> Cons(x#refer_sub ty1 e1, x#refer_sub ty2 e2)
           | _ -> raise (Invalid_formula ("refer",e))
          )
        | _   ->
          let v = x#temp_name in
          x#add_declaration_body (Def(v,ty,e));
          EV v

    method refer ty e = x#refer_sub ty (x#expand e)

    method force f = f (x:>(exp,dec) base)

    method private expand_delay f =
      x#expand (f (x:>(exp,dec) base))

    method private expand_and e1 e2 =
      match x#expand e1 with
      | LB false  -> LB false
      | e1    -> e1 &^ x#expand e2

    method private expand_or e1 e2 =
      match x#expand e1 with
      | LB true -> LB true
      | e1    -> e1 |^ x#expand e2

    method private expand_imp e1 e2 =
      match x#expand e1 with
      | LB false  -> LB true
      | e1    -> e1 =>^ x#expand e2

    method private expand_xor e1 e2 =
      smt_xor (x#expand e1) (x#expand e2)

    method private expand_eq e1 e2 =
      let e1 = x#expand e1 in
      let e2 = x#expand e2 in
      match e1, e2 with
      | If(c,t,e,p), e2 when is_simple e2 -> smt_pre_if c (smt_not c) (t =^ e2) (e =^ e2)
      | e1, If(c,t,e,p) when is_simple e1 -> smt_pre_if c (smt_not c) (e1 =^ t) (e1 =^ e)
      | _ -> e1 =^ e2

    method private ge_purify e1 e2 =
      match e1, e2 with
      | If(c,t,e,false), e2 ->
        let nc = smt_not c in
        let t = x#ge_purify t (simplify_under c e2) in
        let e = x#ge_purify e (simplify_under nc e2) in
        smt_pre_if c nc t e
      | e1, If(c,t,e,false) ->
        let nc = smt_not c in
        let t = x#ge_purify (simplify_under c e1) t in
        let e = x#ge_purify (simplify_under nc e1) e in
        smt_pre_if c nc t e
      | e1, e2 -> e1 >=^ e2
    method private expand_ge e1 e2 =
      x#ge_purify (x#expand e1) (x#expand e2)

    method private gt_purify e1 e2 =
      match e1, e2 with
      | If(c,t,e,false), e2 ->
        let nc = smt_not c in
        let t = x#gt_purify t (simplify_under c e2) in
        let e = x#gt_purify e (simplify_under nc e2) in
        smt_pre_if c nc t e
      | e1, If(c,t,e,false) ->
        let nc = smt_not c in
        let t = x#gt_purify (simplify_under c e1) t in
        let e = x#gt_purify (simplify_under nc e1) e in
        smt_pre_if c nc t e
      | e1, e2 -> e1 >^ e2
    method private expand_gt e1 e2 =
      x#gt_purify (x#expand e1) (x#expand e2)

    method private add_purify e1 e2 =
      match e1, e2 with
      | If(c,t,e,_), _ ->
				let nc = smt_not c in
				let e2 = x#refer_base e2 in
        smt_pre_if c nc (x#add_purify t e2) (x#add_purify e e2)
      | _, If(c,t,e,_) ->
        let nc = smt_not c in
        let e1 = x#refer_base e1 in
        smt_pre_if c nc (x#add_purify e1 t) (x#add_purify e1 e)
      | _ -> e1 +^ e2

    method private expand_add e1 e2 =
      match x#expand e1 with
      | e1  -> x#add_purify e1 (x#expand e2)

    method private expand_sub e1 e2 = Sub (x#expand e1, x#expand e2)

    method private mul_purify e1 e2 =
      match e1, e2 with
      | LI 0, _
      | LR 0.0, _ -> e1
      | _, LI 0
      | _, LR 0.0 -> e2
      | If(c,t,e,_), _ when is_zero t ->
        let nc = smt_not c in
        smt_pre_if c nc t (x#mul_purify e (simplify_under nc e2))
      | If(c,t,e,_), _ when is_zero e ->
        let nc = smt_not c in
        smt_pre_if c nc (x#mul_purify t (simplify_under c e2)) e
      | _, If(c,t,e,_) when is_zero t ->
        let nc = smt_not c in
        smt_pre_if c nc t (x#mul_purify (simplify_under nc e1) e)
      | _, If(c,t,e,_) when is_zero e ->
        let nc = smt_not c in
        smt_pre_if c nc (x#mul_purify (simplify_under nc e1) t) e
      | If(c,t,e,_), _ ->
        let e2 = x#refer_sub base_ty e2 in
        smt_pre_if c (smt_not c) (x#mul_purify t e2) (x#mul_purify e e2)
      | _, If(c,t,e,_) ->
        let e1 = x#refer_sub base_ty e1 in
        smt_pre_if c (smt_not c) (x#mul_purify e1 t) (x#mul_purify e1 e)
      | _ ->
        e1 *^ e2
    method private expand_mul e1 e2 =
      match x#expand e1 with
      | LI 0   -> LI 0
      | LR 0.0 -> LR 0.0
      | e1     -> x#mul_purify e1 (x#expand e2)

    method private zero_one = (* returns (zero, one) *)
      function
      | []  ->
        (LB true, LB false)
      | e::[] ->
        let e = x#refer Bool e in
        (smt_not e,e)
      | e::es ->
        let e = x#refer Bool e in
        let (zero,one) = x#zero_one es in
        let zero = x#refer Bool zero in
        let one = x#refer Bool one in
        (zero &^ smt_not e, (zero &^ e) |^ (one &^ smt_not e))
    method private expand_zero_one es =
      let (zero,one) = x#zero_one es in
      Cons(zero,one)
    method private expand_es1 es =
      let (zero,one) = x#zero_one es in
      one
    method private expand_atmost1 es =
      let (zero,one) = x#zero_one es in
      zero |^ one
    method private expand_od es =
      let (od,_) =
        List.fold_left (fun (od,e1) e2 -> (od &^ (e2 =>^ e1), e2)) (LB true, LB true) es
      in
      od
    method private expand_max =
      let rec distribute es0 =
        function
        | []  -> es0
        | e1::es1 ->
          match x#expand e1 with
          | Max es2 -> distribute (distribute es0 es2) es1
          | Add(e2, Max es2) ->
            let e2 = x#expand e2 in
            distribute (distribute es0 (List.map (fun e3 -> e2 +^ e3) es2)) es1
          | Add(Max es2, e2) ->
            let e2 = x#expand e2 in
            distribute (distribute es0 (List.map (fun e3 -> e3 +^ e2) es2)) es1
          | e2 -> distribute (x#expand e2::es0) es1
      in
      let rec sub eq max =
        function
        | []  -> x#add_assertion eq; max
        | e::es ->
          let e = x#refer base_ty e in
          x#add_assertion (max >=^ e);
          sub ((max =^ e) |^ eq) max es
      in
      fun es ->
        match distribute [] es with
        | []  -> raise (Invalid_formula ("empty max",Nil))
        | [e] -> x#expand e
        | es  -> (* Max (List.map x#expand es)*)
          sub (LB false) (x#temp_variable base_ty) es

    method private expand_car =
      function
      | Cons(e,_) -> x#expand e
      | Dup(_,e)  -> x#expand e
      | Delay(f)  -> x#expand_car (x#force f)
      | If(c,t,e,p) -> x#expand_if c (smt_car t) (smt_car e)
      | e         -> raise (Invalid_formula ("expand_car", e))

    method private expand_cdr =
      function
      | Cons(_,e) -> x#expand e
      | Dup(_,e)  -> x#expand e
      | Delay(f)  -> x#expand_cdr (x#force f)
      | If(c,t,e,p) -> x#expand_if c (smt_cdr t) (smt_cdr e)
      | e     -> raise (Invalid_formula ("expand_cdr", e))

    method private expand_if e1 e2 e3 =
      match x#expand e1 with
      | LB b  -> x#expand (if b then e2 else e3)
      | e1  ->
        match x#expand e2, x#expand e3 with
        | Cons(e4,e5), Cons(e6,e7) ->
          let e1 = x#refer_sub Bool e1 in Cons(smt_if e1 e4 e6, smt_if e1 e5 e7)
        | e2,e3 -> smt_if e1 e2 e3

    method expand =
      function
      | Nil  -> Nil
      | EV v -> EV v
      | LB b -> LB b
      | LI i -> LI i
      | LR r -> LR r
      | And(e1,e2)  -> x#expand_and e1 e2
      | Or(e1,e2)   -> x#expand_or e1 e2
      | Xor(e1,e2)  -> x#expand_xor e1 e2
      | Imp(e1,e2)  -> x#expand_imp e1 e2
      | Not(e)    -> smt_not (x#expand e)
      | Add(e1,e2)  -> x#expand_add e1 e2
      | Sub(e1,e2)  -> x#expand_sub e1 e2
      | Mul(e1,e2)  -> x#expand_mul e1 e2
      | Div(e1,e2)  -> x#expand e1 /^ x#expand e2
      | Mod(e1,e2)  -> smt_mod (x#expand e1) (x#expand e2)
      | Max es    -> x#expand_max es
      | Eq(e1,e2)   -> x#expand_eq e1 e2
      | Ge(e1,e2)   -> x#expand_ge e1 e2
      | Gt(e1,e2)   -> x#expand_gt e1 e2
      | Le(e1,e2)   -> x#expand_ge e2 e1
      | Lt(e1,e2)   -> x#expand_gt e2 e1
      | ForAll(ds,e)  ->
        let branch = x#branch in
        List.iter branch#add_declaration ds;
        branch#close_for_all e
      | Exists(ds,e)  ->
        let branch = x#branch in
        List.iter branch#add_declaration ds;
        branch#close_exists e
      | ZeroOne es  -> x#expand_zero_one es
      | ES1 es    -> x#expand_es1 es
      | AtMost1 es  -> x#expand_atmost1 es
      | OD es     -> x#expand_od es
      | Car e     -> x#expand_car e
      | Cdr e     -> x#expand_cdr e
      | Cons(e1,e2) -> Cons(x#expand e1,x#expand e2)
      | Dup(ty,e)   -> let e = x#refer ty e in Cons(e,e)
      | If(c,t,e,p) -> x#expand_if c t e
      | App es    -> App(List.map x#expand es)
      | Delay f   -> x#expand_delay f
      | e         -> raise (Invalid_formula ("expand",e))
  end
and subcontext =
  object (x)
    inherit context
    val mutable assertion = LB true
    val mutable declarations = []
    method private add_assertion_body e = assertion <- e &^ assertion
    method private add_declaration_body =
      function
      | Def(v,ty,e) ->
        declarations <- Dec(v,ty)::declarations;
        assertion <- EV v =^ e &^ assertion;
      | d ->
        declarations <- d::declarations;
    method close_exists e =
      let e = x#expand e in
      Exists(declarations,assertion &^ e)
    method close_for_all e =
      let e = x#expand e in
      ForAll(declarations,assertion =>^ e)
  end

class virtual solver =
  object
    inherit context
    method virtual init : unit
    method virtual set_logic : string -> unit
    method virtual check : unit
    method virtual get_bool : exp -> bool
    method virtual get_value : exp -> exp
    method virtual dump_value : string list -> out_channel -> unit
    method virtual push : unit
    method virtual pop : unit
    method virtual reset : unit
  end
;;

let smt_apply =
  function
  | [] -> Nil
  | [EV "not"; e] -> Not e
  | [EV "+"; e] -> e
  | [EV "+"; e1; e2] -> Add(e1,e2)
  | [EV "-"; e] -> Neg e
  | [EV "-"; e1; e2] -> Sub(e1,e2)
  | [EV "/"; e1; e2] -> Div(e1,e2)
  | es -> App es

let (<<) s c = s ^ String.make 1 c

class virtual parser =
  let spaces = " \t\n\r" in
  let singles = "()\x00" in
  let breakers = spaces ^ singles in
  object (x)
    val mutable index = 1
    val mutable str = ""
    val mutable len = 0
    method virtual input_line : string
    method private peek_char =
      if index > len then
        try
          str <- x#input_line;
          len <- String.length str;
          index <- 0;
          str.[index]
      with End_of_file -> '\x00'
      else if index = len then
        '\n'
      else
        str.[index]
    method private proceed = index <- index + 1;
    method private trim =
      while String.contains spaces x#peek_char do x#proceed done;
    method get_token =
      x#trim;
      let c = x#peek_char in
      let s = String.make 1 c in
      x#proceed;
      if String.contains singles c then
        s
      else if c = '\"' then
        let rec sub s =
          let c = x#peek_char in
          let s = s << c in
          x#proceed;
          if c = '"' then s else sub s
        in
        sub s
      else
        let rec sub s =
          let c = x#peek_char in
          if String.contains breakers c then
            s
          else
            sub (x#proceed; s << c)
        in
        sub s
    method parse_app =
      let rec sub es =
        match x#peek_char with
        | ')' -> x#proceed; smt_apply es
        | '\x00' -> raise (Parse_error "unexpected EOF")
        | _ -> sub (es @ [x#get_exp])
      in
      sub []
    method get_exp =
      let token = x#get_token in
      match token with
      | "(" -> x#parse_app
      | "true" -> LB true
      | "false" -> LB false
      | "\x00" -> EOF
      | _ -> 
        if Str.string_match (Str.regexp "\\([0-9]+\\)") token 0 then
          let int_part = int_of_string (Str.matched_string token) in
          let next = Str.match_end () in
          if Str.string_match (Str.regexp "\\(\\.0\\)?$") token next then
            LI int_part
          else if Str.string_match (Str.regexp "\\.[0-9]+$") token next then
            LR(float_of_int int_part +. float_of_string (Str.matched_string token))
          else
            raise (Parse_error token)
        else
          EV token
  end

let rec smt_eval_float =
  function
  | LI i -> float_of_int i
  | LR r -> r
  | Neg e -> -.(smt_eval_float e)
  | Div(e1,e2) -> smt_eval_float e1 /. smt_eval_float e2
  | e -> raise (Invalid_formula ("eval_float",e))

let rec smt_eval_int e =
  match e with
  | LI i -> i
  | LR r -> raise (Invalid_formula ("real as int",e))
  | Neg e -> -(smt_eval_int e)
  | e -> raise (Invalid_formula ("eval_int",e))

let test_sat str = Str.string_match (Str.regexp "sat.*") str 0
let test_unsat str = Str.string_match (Str.regexp "un\\(sat\\|known\\).*") str 0

class virtual smt_lib_2_0 =
  object (x)
    inherit Io.t
    inherit solver
    inherit sexp_printer
    inherit parser
    inherit Proc.finalized (fun y -> y#exit)

    val mutable initialized = false

    method exit =
      if initialized then begin
        x#puts "(exit)";
        x#endl;
        x#close;
        initialized <- false
      end;

    method set_logic logic =
      if not initialized then begin
        x#init;
        initialized <- true;
      end;
      x#puts ("(set-logic " ^ logic ^ ")");
      x#endl;

    method private add_declaration_body d =
      match d with
      | Dec(v,ty) ->
        x#puts "(declare-fun ";
        x#pr_v v;
        x#puts " () ";
        x#pr_ty ty;
        x#puts ")";
        x#endl;
      | Def(v,ty,e) ->
        x#puts "(define-fun ";
        x#pr_v v;
        x#puts " () ";
        x#pr_ty ty;
        x#puts " ";
        if  match e with
          | Or(_,_) -> true
          | And(_,_)  -> true
          | Imp(_,_)  -> true
          | _ -> false
        then begin
          x#endl;
          x#enter 2;
          x#pr_e e;
          x#leave 2;
        end else begin
          x#pr_e e;
        end;
        x#puts ")";
        x#endl;
    method private add_assertion_body e =
      x#puts "(assert ";
      x#enter 8;
      x#pr_e e;
      x#leave 8;
      x#puts ")";
      x#endl;
    method check =
      x#puts "(check-sat)";
      x#endl;
      let e = x#get_exp in
      if e = EV "sat" then ()
      else if e = EV "unsat" then begin
        raise Inconsistent
      end else begin
        raise (Response("check-sat",e));
      end;
    method get_bool e =
      match x#get_value e with
      | LB b -> b
      | v -> raise (Response("get_value (bool)",v))
    method get_value v =
      match v with
      | LB _
      | LI _
      | LR _ -> v
      | If(c,t,e,false) ->
        x#get_value (if x#get_bool c then t else e)
      | _ ->
        x#puts "(get-value (";
        x#pr_e (x#expand v);
        x#puts "))";
        x#endl;
        match x#get_exp with
        | App[App[e1;e2]] -> e2
        | e -> raise (Response("get-value",e))
    method dump_value vs os =
      if vs <> [] then
      (
        x#puts "(get-value (";
        List.iter (fun v -> x#pr_v v; x#puts " ") vs;
        x#puts "))";
        x#endl;
        let rec sub =
          function
          | [] -> ()
          | _::vs ->
            let s = x#input_line in
            output_string os (s^"\n");
            sub vs
        in
        sub vs
      )
    method push =
      x#puts "(push)";
      x#endl;
    method pop =
      x#puts "(pop)";
      x#endl;
    method reboot =
      x#puts "(exit)"; x#endl; consistent <- true; temp_names <- 0;
      x#close;
      initialized <- false;
    method reset =
      x#puts "(reset)"; x#endl; consistent <- true; temp_names <- 0;

    method pr_v v =
      let len = String.length v in
      let rec sub i =
        if i < len then begin
          begin
            match v.[i] with
            | 'a'..'z' | 'A'..'Z' | '0'..'9' |  '+' | '-' | '*' | '/'
            | '_' -> x#putc v.[i]
            | ' ' -> x#puts "<sp>"
            | '\''  -> x#puts "<q>"
            | '<' -> x#puts "<gt>"
            | '>' -> x#puts "<lt>"
            | '#' -> x#puts "<sh>"
            | ':' -> x#puts "<col>"
            | '\\'  -> x#puts "<bs>"
            | '.' -> x#puts "<dot>"
            | '{' -> x#puts "<bl>"
            | '}'  -> x#puts "<br>"
            | c   -> x#putc '<'; x#put_hex (Char.code c); x#putc '>'
            end;
          sub (i+1);
        end
      in
      sub 0
    method pr_ty =
      function
      | Int -> x#puts "Int";
      | Real  -> x#puts "Real";
      | Bool  -> x#puts "Bool";
      | _   -> raise (Internal "type");
    method pr_ds =
      let pr_d =
        function
        | Dec(v,ty) -> x#pr_v v; x#puts " "; x#pr_ty ty;
        | _     -> raise (Internal "dec");
      in
      function
      | []  -> ()
      | d::[] -> x#puts "("; pr_d d; x#puts ")";
      | d::ds -> x#puts "("; pr_d d; x#puts ") "; x#pr_ds ds;
  end

let create_solver debug_to debug_in debug_out command options =
  object (x)
    inherit smt_lib_2_0
    val main = new Proc.t command options
    val dout = if debug_out then new Io.pretty_wrap_out debug_to else (Io.null :> Io.printer)
    val din = if debug_in then new Io.pretty_wrap_out debug_to else (Io.null :> Io.printer)
    method endl = main#endl; dout#endl;
    method putc c = main#putc c; dout#putc c;
    method puts s = main#puts s; dout#puts s;
    method enter n = dout#enter n;
    method leave n = dout#leave n;
    method enter_inline = dout#enter_inline;
    method leave_inline = dout#leave_inline;
    method ready = main#ready;
    method flush = main#flush; dout#flush;
    method close = main#close; dout#close;
    method init = main#init;

    method input_line =
      din#puts "< ";
      din#flush;
      let s = main#input_line in
      din#puts s;
      din#endl;
      s
  end

let debug_exp e = if params.debug2 then (prerr_exp e; e) else e

