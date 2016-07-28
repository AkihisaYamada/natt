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
		method refer_base e = x#refer base_ty e
		method virtual expand : 'e -> 'e
	end;;

type exp =
	| EOF
	| Nil
	| NegInf
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
	| If of exp * exp * exp
	| PB of exp
	| Vec of exp list
	| Mat of exp list list
	| App of exp list
and dec =
	| Dec of name * ty
	| Def of name * ty * exp
;;

exception Inconsistent
exception Internal of string
exception Invalid_formula of string
exception Response of string * exp

let rec is_simple =
	function
	| Nil		-> true
	| EV _		-> true
	| LI _		-> true
	| LB _		-> true
	| LR _		-> true
	| PB(EV _)	-> true
	| Not(EV _)	-> true
(*	| And(e1,e2)-> is_simple e1 && is_simple e2
	| Or(e1,e2)	-> is_simple e1 && is_simple e2
*)	| Eq(e1,e2)	-> is_simple e1 && is_simple e2
	| Gt(e1,e2)	-> is_simple e1 && is_simple e2
	| Ge(e1,e2)	-> is_simple e1 && is_simple e2
	| _			-> false

let rec simple_eq e1 e2 =
	match e1, e2 with
	| Nil, Nil -> true
	| NegInf, NegInf -> true
	| EV v1, EV v2	-> v1 = v2
	| LB b1, LB b2	-> b1 = b2
	| LI i1, LI i2	-> i1 = i2
	| LR r1, LR r2	-> r1 = r2
	| Not(EV v1), Not(EV v2) -> v1 = v2
	| PB(EV v1), PB(EV v2) -> v1 = v2
	| Ge(l1,r1),Ge(l2,r2) -> simple_eq l1 l2 && simple_eq r1 r2
	| Gt(l1,r1),Gt(l2,r2) -> simple_eq l1 l2 && simple_eq r1 r2
	| Eq(l1,r1),Eq(l2,r2) -> simple_eq l1 l2 && simple_eq r1 r2 || simple_eq l1 r2 && simple_eq r1 l2
	| _ -> false

let smt_expand e f =
	if is_simple e then f e else Delay(fun context -> f (context#expand e))

let smt_let ty e f =
	if is_simple e then f e else Delay(fun context -> f (context#refer ty e))

let rec smt_not =
	function
	| LB b	-> LB (not b)
	| Not e	-> e
	| Gt(e1,e2) -> Ge(e2,e1)
	| Ge(e1,e2) -> Gt(e2,e1)
	| Or(e1,e2) -> And(smt_not e1, smt_not e2)
	| And(e1,e2) -> Or(smt_not e1, smt_not e2)
	| e		-> Not(e)

let smt_pb =
	function
	| LB b	-> LI(if b then 1 else 0)
	| e		-> PB e

let rec (+^) e1 e2 =
	match e1, e2 with
	| LI 0,  _		-> e2
	| LR 0.0, _		-> e2
	| _, LI 0		-> e1
	| _, LR 0.0		-> e1
	| LI i1, LI i2	-> LI(i1 + i2)
	| LR r1, LR r2	-> LR(r1 +. r2)
	| Max es1, _	-> Max(List.map (fun e1 -> e1 +^ e2) es1)
	| _, Max es2	-> Max(List.map (fun e2 -> e1 +^ e2) es2)
	| Vec u, Vec v	-> Vec(Matrix.sum_vec (+^) u v)
	| Vec u, _		-> Vec(List.map (fun e -> e +^ e2) u)
	| _, Vec u		-> Vec(List.map (fun e -> e1 +^ e) u)
	| Mat m, Mat n	-> Mat(Matrix.sum (+^) m n)
	| Mat m, _		-> Mat(Matrix.mapij (fun i j e -> if i = j then e +^ e2 else e) m)
	| _, Mat m		-> Mat(Matrix.mapij (fun i j e -> if i = j then e1 +^ e else e) m)
	| PB c, _		-> if is_simple e2 then If(c, LI 1 +^ e2, e2) else Add(e1,e2)
	| _, PB c		-> if is_simple e1 then If(c, e1 +^ LI 1, e1) else Add(e1,e2)
	| If(c,t,e),_	-> if is_simple e2 then If(c, t +^ e2, e +^ e2) else Add(e1,e2)
	| _,If(c,t,e)	-> if is_simple e1 then If(c, e1 +^ t, e1 +^ e) else Add(e1,e2)
	| Add(e3,e4),_	-> Add(e3, e4 +^ e2)
	| _				-> Add(e1,e2)

let (-^) e1 e2 = Sub(e1,e2)

let simple_ge e1 e2 =
	match e1, e2 with
	| EV v1, EV v2 -> v1 = v2
	| LI i1, LI i2 -> i1 >= i2
	| LR r1, LR r2 -> r1 >= r2
	| _ -> false

let rec simplify_under e1 e2 =
	match e1, e2 with
	| _, LB _
	| _, LI _
	| _, LR _ -> e2
	| _, PB e3 -> smt_pb (simplify_under e1 e3)
	| _, Add(e3,e4) -> simplify_under e1 e3 +^ simplify_under e1 e4
	| _, Mul(e3,e4) -> simplify_under e1 e3 *^ simplify_under e1 e4
	| _, And(e3,e4) -> (
		let e3 = simplify_under e1 e3 in
		if e3 = LB false then e3
		else
			let e4 = simplify_under e1 e4 in
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
			if e3 = LB false then e4
			else if e4 = LB false then e3
			else if e4 = LB true then e4
			else if simple_eq e3 e4 then e3
			else Or(e3,e4)
	)
	| _, If(e3,e4,e5) -> (
		match simplify_under e1 e3 with
		| LB b -> if b then simplify_under e1 e4 else simplify_under e1 e5
		| e3 ->
			(* e4 and e5 should be already simplified w.r.t. e3 *)
			If(e3, simplify_under e1 e4, simplify_under e1 e5)
	)
	| And(e3,e4), _ -> simplify_under e3 (simplify_under e4 e2)
	| Not e3, _ ->
		if simple_eq e3 e2 then LB false else e2
	| Eq(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge r2 l1 && simple_ge r1 l2 then LB false else Gt(l2,r2)
	| Eq(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge l2 l1 && simple_ge r1 r2 then LB true else Ge(l2,r2)
	| Gt(l1,r1), Eq(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge l2 l1 && simple_ge r1 r2 ||
		   simple_ge r2 l1 && simple_ge r1 l2 then LB false
		else Eq(l2,r2)
	| Gt(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge l2 l1 && simple_ge r1 r2 then LB true
		else if simple_ge r2 l1 && simple_ge r1 l2 then LB false
		else Gt(l2,r2)
	| Gt(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge l2 l1 && simple_ge r1 r2 then LB true
		else if simple_ge r2 l1 && simple_ge r1 l2 then LB false
		else Ge(l2,r2)
	| Ge(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge l2 l1 && simple_ge r1 r2 then LB true
		else if simple_ge r2 l1 && simple_ge r1 l2 then Eq(l2,r2)
		else Ge(l2,r2)
	| Ge(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if simple_ge r2 l1 && simple_ge r1 l2 then LB false
		else Gt(l2,r2)
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
and ( *^) e1 e2 =
	match e1, e2 with
	| LI 0, _		-> e1
	| LI 1, _		-> e2
	| _, LI 0		-> e2
	| _, LI 1		-> e1
	| LI i1, LI i2	-> LI(i1*i2)
	| Mat m, Mat n	-> Mat(Matrix.prod (+^) ( *^) (LI 0) m n)
	| Mat m, Vec v	-> Vec(Matrix.prod_vec (+^) ( *^) (LI 0) m v)
	| Mat m, _		-> Mat(List.map (List.map (fun e -> e *^ e2)) m)
	| _, Mat m		-> Mat(List.map (List.map (fun e -> e1 *^ e)) m)
	| Vec u, _		-> Vec(List.map (fun e -> e *^ e2) u)
	| _, Vec u		-> Vec(List.map (fun e -> e1 *^ e) u)
	| PB e1, _		-> pb_distribute e1 e2
	| _, PB e2		-> pb_distribute e2 e1
	| If(c,e,LI 0), _ ->
		let e2 = simplify_under c e2 in
		let e3 = e *^ e2 in
		if e3 = LI 0 then e3 else If(c,e3,LI 0)
	| _, If(c,e,LI 0) ->
		let e1 = simplify_under c e1 in
		let e3 = e1 *^ e in
		if e3 = LI 0 then e3 else If(c,e3,LI 0)
	| _				-> Mul(e1,e2)
and pb_distribute e1 e2 =
	match e1 with
	| LB b	-> if b then e2 else LI 0
	| _ ->
		match e2 with
		| LI 0			-> LI 0
		| PB e2			-> smt_pb (e1 &^ e2)
		| Mul(PB e2,e3) -> pb_distribute (e1 &^ e2) e3
		| Mul(e2,PB e3)	-> pb_distribute (e1 &^ e3) e2
		| e2			-> Mul(smt_pb e1, e2)
and smt_if e1 e2 e3 =
	match e1 with
	| LB b	-> if b then e2 else e3
	| _		->
		let ne1 = smt_not e1 in
		match simplify_under e1 e2, simplify_under ne1 e3 with
		| LB b2, e3	-> if b2 then e1 |^ e3 else ne1 &^ e3
		| e2, LB b3	-> if b3 then e1 =>^ e2 else e1 &^ e2
		| e2, e3 ->
			if simple_eq e2 e3 then e2
			else if e2 = LI 0 then If(ne1, e3, e2) (* '0' is always the 'else' case *)
			else If(e1,e2,e3)

let (/^) e1 e2 =
	if e1 = LI 0 || e2 = LI 1 then e1
	else Div(e1,e2)

let smt_xor e1 e2 =
	match e1, e2 with
	| LB b, _ -> if b then smt_not e2 else e2
	| _, LB b -> if b then smt_not e1 else e1
	| _ ->
		if simple_eq e1 e2 then LB false
		else if simple_eq e1 (smt_not e2) then LB true
		else Xor(e1,e2)


let smt_for_all f = List.fold_left (fun ret e -> ret &^ f e) (LB true)

let smt_for_all2 f = List.fold_left2 (fun ret e1 e2 -> ret &^ f e1 e2) (LB true)

let smt_exists f = List.fold_left (fun ret e -> ret |^ f e) (LB false)

let vector_scalar comp es1 e2 context =
	let e2 = context#refer Int e2 in
	List.fold_left (fun ret e1 -> ret &^ comp e1 e2) (LB true) es1

let scalar_vector comp e1 es2 context =
	let e1 = context#refer Int e1 in
	List.fold_left (fun ret e2 -> ret &^ comp e1 e2) (LB true) es2

let matrix_scalar comp ess1 e2 context =
	let e2 = context#refer Int e2 in
	Matrix.foldij (fun ret i j e1 -> ret &^ comp e1 (if i = j then e2 else LI 0)) (LB true) ess1

let scalar_matrix comp e1 ess2 context =
	let e1 = context#refer Int e1 in
	Matrix.foldij (fun ret i j e2 -> ret &^ comp (if i = j then e1 else LI 0) e2) (LB true) ess2

let rec (=^) e1 e2 =
	match e1, e2 with
	| LI i1, LI i2	-> LB (i1 = i2)
	| PB e1, PB e2	-> e2 =^ e1
	| LI i1, PB e2 	-> if i1 = 1 then e2 else if i1 = 0 then smt_not e2 else LB false
	| PB e1, LI i2 	-> if 1 = i2 then e1 else if 0 = i2 then smt_not e1 else LB false
	| Vec u, Vec v	-> smt_for_all2 (=^) u v
	| Vec u, e2		-> Delay(vector_scalar (=^) u e2)
	| e1, Vec u		-> Delay(scalar_vector (=^) e1 u)
	| Mat m, Mat n	-> smt_for_all2 (smt_for_all2 (=^)) m n
	| Mat m, e2		-> Delay(matrix_scalar (=^) m e2)
	| e1, Mat n		-> Delay(scalar_matrix (=^) e1 n)
	| _				-> if simple_eq e1 e2 then LB true else Eq(e1,e2)

let (<>^) e1 e2 = smt_not (e1 =^ e2)

let rec (>=^) e1 e2 =
	match e1, e2 with
	| LI i1, LI i2	-> LB(i1 >= i2)
	| LR r1, LR r2	-> LB(r1 >= r2)
	| LI i1, PB e2 	-> if i1 >= 1 then LB true else if i1 = 0 then Not e2 else LB false
	| PB e1, LI i2 	-> if 0 >= i2 then LB true else if 1 = i2 then e1 else LB false
	| PB e1, PB e2	-> e2 =>^ e1
	| Vec v1, Vec v2-> smt_for_all2 (>=^) v1 v2
	| Vec v1, _		-> Delay(vector_scalar (>=^) v1 e2)
	| _, Vec v2		-> Delay(scalar_vector (>=^) e1 v2)
	| Mat m1, Mat m2-> smt_for_all2 (smt_for_all2 (>=^)) m1 m2
	| Mat m1, _		-> Delay(vector_scalar (>=^) (Matrix.diag_elems m1) e2)
	| _, Mat m2		-> Delay(scalar_matrix (>=^) e1 m2)
	| _				-> if simple_eq e1 e2 then LB true else Ge(e1,e2)

let rec (>^) e1 e2 =
	match e1, e2 with
	| LI i1, LI i2 -> LB(i1 > i2)
	| LR r1, LR r2 -> LB(r1 > r2)
	| PB e1, PB e2	-> e1 &^ smt_not e2
	| PB e1, LI i	-> if i = 0 then e1 else LB false
	| Vec(e1::v1), Vec(e2::v2) -> (e1 >^ e2) &^ smt_for_all2 (>=^) v1 v2
	| Vec(e1::v1), _ ->
		smt_let Int e2 (fun e2 -> (e1 >^ e2) &^ smt_for_all (fun e1 -> e1 >=^ e2) v1)
	| _, Vec(e2::v2)		->
		smt_let Int e1 (fun e1 -> (e1 >^ e2) &^ smt_for_all (fun e2 -> e1 >=^ e2) v2)
	| _				-> if simple_eq e1 e2 then LB false else Gt(e1,e2)

let (<=^) e1 e2 = e2 >=^ e1
let (<^) e1 e2 = e2 >^ e1

let smt_mod e1 e2 = Mod(e1,e2)
let smt_max e1 e2 =
	match e1, e2 with
	| NegInf, _		-> e2
	| _, NegInf		-> e1
	| LI i1, LI i2	-> LI(if i1 > i2 then i1 else i2)
	| PB b1, PB b2	-> smt_pb (b1 |^ b2)
	| _, Max es2	-> Max(e1::es2)
	| Max es1,_		-> Max(e2::es1)
	| _,_			-> Max[e1;e2]

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
	| _ -> smt_expand e (function Cons(e1,e2) -> f e1 e2 | _ -> raise (Invalid_formula "smt_split"))

let arctic_add e1 e2 =
	match e1, e2 with
	| Mat m, Mat n	-> Mat(Matrix.sum smt_max m n)
	| Vec u, Vec v	-> Vec(Matrix.sum_vec smt_max u v)
	| _				-> smt_max e1 e2

let arctic_mul e1 e2 =
	match e1, e2 with
	| Mat m, Mat n	-> Mat(Matrix.prod smt_max (+^) NegInf m n)
	| Mat m, Vec v	-> Vec(Matrix.prod_vec smt_max (+^) NegInf m v)
	| _				-> e1 +^ e2


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
				| And(e1,e2)	-> sub e1; sub e2;
				| LB true		-> ();
				| e ->
					x#add_assertion_body e;
					if e = LB false then (consistent <- false; raise Inconsistent);
			in
			fun e -> if consistent then sub (x#expand e);

		method add_declaration d =
			if consistent then begin
				let d =
					match d with
					| Def(v,ty,e)	-> Def(v,ty,x#expand e)
					| _	-> d
				in
				x#add_declaration_body d;
			end
		method add_definition v ty e = x#add_declaration (Def(v,ty,e))

		method add_variable v ty = x#add_declaration (Dec(v,ty))

		method new_variable v ty = x#add_variable v ty; EV v

		val mutable temp_names = 0
		method private temp_name =
			let	v = "_" ^ string_of_int temp_names in
			temp_names <- temp_names + 1;
			v

		method temp_variable ty =
			x#new_variable x#temp_name ty

		method private refer_sub ty e =
			if not params.tmpvar || not consistent || is_simple e then e
			else
				match e with
				| Vec es	-> Vec(List.map (x#refer_sub ty) es)
				| Mat ess	-> Mat(List.map (List.map (x#refer_sub ty)) ess)
				| Cons(e1,e2) ->
					(match ty with
					 | Prod(ty1,ty2) -> Cons(x#refer_sub ty1 e1, x#refer_sub ty2 e2)
					 | _ -> raise (Invalid_formula "refer")
					)
				| PB e	-> PB((*x#refer_sub Bool *)e)
				| _		->
					let v = x#temp_name in
					x#add_declaration_body (Def(v,ty,e));
					EV v

		method refer ty e = x#refer_sub ty (x#expand e)

		method force f = f (x:>(exp,dec) base)

		method private expand_delay f =
			x#expand (f (x:>(exp,dec) base))

		method private expand_and e1 e2 =
			match x#expand e1 with
			| LB false	-> LB false
			| e1		-> e1 &^ x#expand e2

		method private expand_or e1 e2 =
			match x#expand e1 with
			| LB true	-> LB true
			| e1		-> e1 |^ x#expand e2

		method private expand_imp e1 e2 =
			match x#expand e1 with
			| LB false	-> LB true
			| e1		-> e1 =>^ x#expand e2

		method private expand_xor e1 e2 =
			smt_xor (x#expand e1) (x#expand e2)

		method private expand_eq e1 e2 =
			x#expand e1 =^ x#expand e2

		method private expand_ge e1 e2 = x#expand e1 >=^ x#expand e2

		method private expand_gt e1 e2 = x#expand e1 >^ x#expand e2

		method private expand_add e1 e2 = x#expand e1 +^ x#expand e2

		method private expand_sub e1 e2 = x#expand e1 -^ x#expand e2

		method private mul_if e1 e2 =
			match e1, e2 with
			| _, LI 0 -> e2
			| If(c,t,e), _ ->
				if t = LI 0 then
					If(c, t, x#mul_if e e2)
				else if e = LI 0 then
					If(c, x#mul_if t e2, e)
				else
					let e2 = x#refer_sub base_ty e2 in
					If(c, x#mul_if t e2, x#mul_if e e2)
			| _, If(c,t,e) ->
				if t = LI 0 then
					If(c, t, x#mul_if e1 e)
				else if e = LI 0 then
					If(c, x#mul_if e1 t, e)
				else
					let e1 = x#refer_sub base_ty e1 in
					If(c, x#mul_if e1 t, x#mul_if e1 e)
			| _ ->
				e1 *^ e2
		method private expand_mul e1 e2 =
			match x#expand e1 with
			| LI 0	-> LI 0
			| e1	-> x#mul_if e1 (x#expand e2)

		method private zero_one = (* returns (zero, one) *)
			function
			| []	->
				(LB true, LB false)
			| e::[]	->
				let e = x#refer Bool e in
				(smt_not e,e)
			| e::es	->
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
				| []	-> es0
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
				| []	-> x#add_assertion eq; max
				| e::es	->
					let e = x#refer base_ty e in
					x#add_assertion (max >=^ e);
					sub ((max =^ e) |^ eq) max es
			in
			fun es ->
				match distribute [] es with
				| []	-> raise (Invalid_formula "empty max")
				| [e]	-> x#expand e
				| es	-> (* Max (List.map x#expand es)*)
					sub (LB false) (x#temp_variable base_ty) es

		method private expand_car =
			function
			| Cons(e,_)	-> x#expand e
			| Dup(_,e)	-> x#expand e
			| Delay(f)	-> x#expand_car (x#force f)
			| If(c,t,e) -> x#expand_if c (smt_car t) (smt_car e)
			| e			-> raise (Invalid_formula "car")
		method private expand_cdr =
			function
			| Cons(_,e)	-> x#expand e
			| Dup(_,e)	-> x#expand e
			| Delay(f)	-> x#expand_cdr (x#force f)
			| If(c,t,e)	-> x#expand_if c (smt_cdr t) (smt_cdr e)
			| e			-> raise (Invalid_formula "cdr")
		method private expand_pb e =
			match x#expand e with
			| LB t	-> if t then LI 1 else LI 0
			| e		-> PB e

		method private expand_if e1 e2 e3 =
			match x#expand e1 with
			| LB b	-> x#expand (if b then e2 else e3)
			| e1	->
				match x#expand e2, x#expand e3 with
				| Cons(e4,e5), Cons(e6,e7) -> let e1 = x#refer_sub Bool e1 in Cons(smt_if e1 e4 e6, smt_if e1 e5 e7)
				| Vec u, Vec v -> let e1 = x#refer_sub Bool e1 in Vec(List.map2 (smt_if e1) u v)
				| e2,e3 -> smt_if e1 e2 e3

		method expand =
			function
			| Nil			-> Nil
			| EV v			-> EV v
			| LB b			-> LB b
			| LI i			-> LI i
			| LR r			-> LR r
			| And(e1,e2)	-> x#expand_and e1 e2
			| Or(e1,e2)		-> x#expand_or e1 e2
			| Xor(e1,e2)	-> x#expand_xor e1 e2
			| Imp(e1,e2)	-> x#expand_imp e1 e2
			| Not(e)		-> smt_not (x#expand e)
			| Add(e1,e2)	-> x#expand_add e1 e2
			| Sub(e1,e2)	-> x#expand_sub e1 e2
			| Mul(e1,e2)	-> x#expand_mul e1 e2
			| Div(e1,e2)	-> x#expand e1 /^ x#expand e2
			| Mod(e1,e2)	-> smt_mod (x#expand e1) (x#expand e2)
			| Max es		-> x#expand_max es
			| Eq(e1,e2)		-> x#expand_eq e1 e2
			| Ge(e1,e2)		-> x#expand_ge e1 e2
			| Gt(e1,e2)		-> x#expand_gt e1 e2
			| Le(e1,e2)		-> x#expand e1 <=^ x#expand e2
			| Lt(e1,e2)		-> x#expand e1 <^ x#expand e2
			| ForAll(ds,e)	->
				let branch = x#branch in
				List.iter branch#add_declaration ds;
				branch#close_for_all e
			| Exists(ds,e)	->
				let branch = x#branch in
				List.iter branch#add_declaration ds;
				branch#close_exists e
			| ZeroOne es	-> x#expand_zero_one es
			| ES1 es		-> x#expand_es1 es
			| AtMost1 es	-> x#expand_atmost1 es
			| OD es			-> x#expand_od es
			| Car e			-> x#expand_car e
			| Cdr e			-> x#expand_cdr e
			| Cons(e1,e2)	-> Cons(x#expand e1,x#expand e2)
			| Dup(ty,e)		-> let e = x#refer ty e in Cons(e,e)
			| If(e1,e2,e3)	-> x#expand_if e1 e2 e3
			| PB e			-> x#expand_pb e
			| App es		-> App(List.map x#expand es)
			| Vec es		-> Vec(List.map x#expand es)
			| Mat ess		-> Mat(List.map (List.map x#expand) ess)
			| Delay f		-> x#expand_delay f
			| _				-> raise (Invalid_formula "expansion")
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

class virtual solver_frame =
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
				| []	-> ();
				| [e]	-> put e;
				| e::es	-> put e; pr punc; withpunc put punc es
			in
			let rec pr_and =
				function
				| And(e1,e2) -> pr_and e1; x#endl; pr_and e2;
				| e	-> pr_e e;
			in
			let rec pr_or =
				function
				| Or(e1,e2) -> pr_or e1; x#endl; pr_or e2;
				| e	-> pr_e e;
			in
			let rec pr_xor =
				function
				| Xor(e1,e2) -> pr_xor e1; x#endl; pr_xor e2;
				| e	-> pr_e e;
			in
			let rec pr_add =
				function
				| Add(e1,e2) -> pr_add e1; pr " "; pr_add e2;
				| e	-> pr_e e;
			in
			let rec pr_mul =
				function
				| Mul(e1,e2) -> pr_mul e1; pr " "; pr_mul e2;
				| e	-> pr_e e;
			in
			match e with
			| EOF			-> pr "<EOF>";
			| Nil			-> pr "()";
			| NegInf		-> pr "-INF";
			| EV v			-> x#pr_v v;
			| LI i			-> if i < 0 then (pr "(- "; pr_i (-i); pr ")";) else pr_i i;
			| LR r			-> if r < 0.0 then (pr "(- "; pr_f (-. r); pr ")";) else pr_f r;
			| LB b			-> pr (if b then "true" else "false");
			| Add(e1,e2)	-> pr "(+ "; pr_add e1; pr " "; pr_add e2; pr ")";
			| Sub(e1,e2)	-> pr "(- "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Neg e1		-> pr "(- "; pr_e e1; pr ")";
			| Mul(PB(e1),e2)-> pr_e (If(e1,e2,LI 0))
			| Mul(e1,PB(e2))-> pr_e (If(e2,e1,LI 0))
			| Mul(e1,e2)	-> pr "(* "; pr_mul e1; pr " "; pr_mul e2; pr ")";
			| Div(e1,e2)	-> pr "(/ "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Mod(e1,e2)	-> pr "(mod "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Eq(e1,e2)		-> pr "(= "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Ge(e1,e2)		-> pr "(>= "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Gt(e1,e2)		-> pr "(> "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Le(e1,e2)		-> pr "(<= "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Lt(e1,e2)		-> pr "(< "; pr_e e1; pr " "; pr_e e2; pr ")";
			| And(e1,e2)	-> x#enter 5;
							   pr "(and "; pr_and e1; x#endl; pr_and e2; pr ")";
							   x#leave 5;
			| Or(e1,e2)		-> x#enter 4;
							   pr "(or "; pr_or e1; x#endl; pr_or e2; pr ")";
							   x#leave 4;
			| Xor(e1,e2)	-> x#enter 5;
							   pr "(xor "; pr_xor e1; x#endl; pr_xor e2; pr ")";
							   x#leave 5;
			| Not e1		-> x#enter 5; pr "(not "; pr_e e1; pr ")"; x#leave 5;
			| Imp(e1,e2)	-> x#enter 4; pr "(=> "; pr_e e1; x#endl; pr_e e2; pr ")"; x#leave 4;
			| ForAll(ds,e)	-> x#enter 7;
							   pr "(forall ("; x#pr_ds ds; pr ")"; x#endl;
							   pr_e e; pr ")"; x#endl;
							   x#leave 7;
			| Exists(ds,e)	-> x#enter 7;
							   pr "(exists ("; x#pr_ds ds; pr ") ";
							   pr_e e; pr ")"; x#endl;
							   x#leave 7;
			| Cons(e1,e2)	-> pr "(cons "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Dup(_,e)		-> pr "(dup "; pr_e e; pr ")";
			| Car(e)		-> pr "(car "; pr_e e; pr ")";
			| Cdr(e)		-> pr "(cdr "; pr_e e; pr ")";
			| If(e1,e2,e3)	-> x#enter_inline;
							   pr "(ite "; pr_e e1; pr " "; pr_e e2; pr " "; pr_e e3; pr ")";
							   x#leave_inline;
			| Max(es)		-> pr "(max"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| ZeroOne(es)	-> pr "(zeroone"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| ES1(es)		-> pr "(es1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| AtMost1(es)	-> pr "(atmost1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| OD(es)		-> pr "(od"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| App(es)		-> pr "("; withpunc pr_e " " es; pr ")";
			| Delay f		-> pr "(delay...)";
			| PB(e)			-> pr_e (If(e, LI 1, LI 0));
			| Vec(es)		-> pr "["; withpunc pr_e ";" es; pr "]";
			| Mat(ess)		-> pr "["; withpunc (withpunc pr_e ",") ";" ess; pr "]";
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

let output_exp (pr : #Io.printer) = (new sexp_printer_wrap pr)#pr_e

let prerr_exp = output_exp Io.cerr

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
				| '\x00' -> raise (Invalid_formula "parse error")
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
						raise (Invalid_formula "parse error")
				else
					EV token
	end

let rec smt_eval_float =
	function
	| LI i -> float_of_int i
	| LR r -> r
	| Neg e -> -.(smt_eval_float e)
	| Div(e1,e2) -> smt_eval_float e1 /. smt_eval_float e2
	| _ -> raise (Invalid_formula "value")

let rec smt_eval_int =
	function
	| LI i -> i
	| LR r -> raise (Invalid_formula "real as int")
	| Neg e -> -(smt_eval_int e)
	| Div(e1,e2) -> raise (Invalid_formula "rational as int")
	| _ -> raise (Invalid_formula "value")

let test_sat str = Str.string_match (Str.regexp "sat.*") str 0
let test_unsat str = Str.string_match (Str.regexp "un\\(sat\\|known\\).*") str 0

class virtual smt_lib_2_0 =
	object (x)
		inherit Io.t
		inherit solver_frame
		inherit sexp_printer
		inherit parser
		inherit Proc.finalized (fun y -> y#exit)

		val mutable initialized = false

		method exit =
			if initialized then begin
				x#puts "(exit)\n";
				x#flush;
				x#close;
				initialized <- false
			end;

		method set_logic logic =
			if not initialized then begin
				x#init;
				initialized <- true;
			end;
			x#puts ("(set-logic " ^ logic ^ ")\n");

		method private add_declaration_body d =
			match d with
			| Dec(v,ty) ->
				x#puts "(declare-fun ";
				x#pr_v v;
				x#puts " () ";
				x#pr_ty ty;
				x#puts ")\n";
			| Def(v,ty,e) ->
				x#puts "(define-fun ";
				x#pr_v v;
				x#puts " () ";
				x#pr_ty ty;
				x#puts " ";
				if	match e with
					| Or(_,_)	-> true
					| And(_,_)	-> true
					| Imp(_,_)	-> true
					| _ -> false
				then begin
					x#enter 2;
					x#endl;
					x#pr_e e;
					x#leave 2;
				end else begin
					x#pr_e e;
				end;
				x#puts ")\n";
		method private add_assertion_body e =
			x#puts "(assert ";
			x#enter 8;
			x#pr_e e;
			x#leave 8;
			x#puts ")\n";
			x#flush;
		method check =
			x#puts "(check-sat)\n";
			x#flush;
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
		method get_value =
			function
			| Vec(es) -> Vec(List.map x#get_value es)
			| Mat(ess) -> Mat(List.map (List.map x#get_value) ess)
(*			| If(c,t,e) -> if x#get_value c = LB true then x#get_value t else x#get_value e
*)			| v ->
				x#puts "(get-value (";
				x#pr_e (x#expand v);
				x#puts "))\n";
				x#flush;
				let e = x#get_exp in
				match e with
				| App[App[e1;e2]] -> e2
				| _ -> raise (Response("get-value",e))
		method dump_value vs os =
			if vs <> [] then
			(
				x#puts "(get-value (";
				List.iter (fun v -> x#pr_v v; x#puts " ") vs;
				x#puts "))\n";
				x#flush;
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
			x#puts "(push)\n";
			x#flush;
		method pop =
			x#puts "(pop)\n";
			x#flush;
		method reboot =
			x#puts "(exit)\n"; x#flush; consistent <- true; temp_names <- 0;
			x#close;
			initialized <- false;
		method reset =
			x#puts "(reset)\n"; x#flush; consistent <- true; temp_names <- 0;

		method pr_v v =
			let len = String.length v in
			let rec sub i =
				if i < len then begin
					begin
						match v.[i] with
						| 'a'..'z' | 'A'..'Z' | '0'..'9' |  '+' | '-' | '*' | '/'
						| '_' -> x#putc v.[i]
						| ' '	-> x#puts "<sp>"
						| '\''	-> x#puts "<q>"
						| '<'	-> x#puts "<gt>"
						| '>'	-> x#puts "<lt>"
						| '#'	-> x#puts "<sh>"
						| ':'	-> x#puts "<col>"
						| '\\'	-> x#puts "<bs>"
						| '.'	-> x#puts "<dot>"
						| '{'	-> x#puts "<bl>"
						| '}'  -> x#puts "<br>"
						| c		-> x#putc '<'; x#put_hex (Char.code c); x#putc '>'
						end;
					sub (i+1);
				end
			in
			sub 0
		method pr_ty =
			function
			| Int	-> x#puts "Int";
			| Real	-> x#puts "Real";
			| Bool	-> x#puts "Bool";
			| _		-> raise (Internal "type");
		method pr_ds =
			let pr_d =
				function
				| Dec(v,ty) -> x#pr_v v; x#puts " "; x#pr_ty ty;
				| _			-> raise (Internal "dec");
			in
			function
			| []	-> ()
			| d::[]	-> x#puts "("; pr_d d; x#puts ")";
			| d::ds	-> x#puts "("; pr_d d; x#puts ") "; x#pr_ds ds;
	end

let create_solver debug_to debug_in debug_out command options =
	let main = object
			inherit smt_lib_2_0
			inherit Proc.t command options
		end
	in
	match debug_in, debug_out with
	| true, true ->
		object (x)
			inherit smt_lib_2_0
			inherit Proc.t command options
			inherit Io.debug_out main debug_to
			inherit Io.debug_in main debug_to
		end
	| true, false ->
		object (x)
			inherit smt_lib_2_0
			inherit Proc.t command options
			inherit Io.debug_in main debug_to
		end
	| false, true ->
		object (x)
			inherit smt_lib_2_0
			inherit Proc.t command options
			inherit Io.debug_out main debug_to
		end
	| _ ->
		main

let debug_exp e = if params.debug2 then (prerr_exp e; e) else e

