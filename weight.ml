open Sym
open Term
open Smt
open Util
open Preorder
open Params
open Io
open Strategy

type 'a t =
| BVar of 'a * range
| Smt of exp
| Prod of 'a t list
| Sum of 'a t list
| Max of 'a t list
| Cond of exp * 'a t * 'a t

let zero_w = Smt (LI 0)
let one_w = Smt (LI 1)

let sum =
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [] -> zero_w | [w] -> w | _ -> Sum acc)
		| Smt e :: ws -> sub2 e acc ws
		| Sum ws1 :: ws -> sub acc (ws1 @ ws)
		| w :: ws -> sub (w::acc) ws
	and sub2 e acc ws =
		match ws with
		| [] -> (match acc with [] -> Smt e | _ -> Sum(Smt e :: acc))
		| Smt e1 :: ws -> sub2 (e +^ e1) acc ws
		| Sum ws1 :: ws -> sub2 e acc (ws1 @ ws)
		| w :: ws -> sub2 e (w::acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let prod =
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [] -> one_w | [w] -> w | _ -> Prod acc)
		| Smt e :: ws -> if is_zero e then zero_w else sub2 e acc ws
		| Prod ws1 :: ws -> sub acc (ws1 @ ws)
		| w :: ws -> sub (w::acc) ws
	and sub2 e acc ws =
		match ws with
		| [] -> (match acc with [] -> Smt e | _ -> Prod (Smt e::acc))
		| Smt e1 :: ws -> if is_zero e1 then zero_w else sub2 (e *^ e1) acc ws
		| Prod ws1 :: ws -> sub2 e acc (ws1 @ ws)
		| w :: ws -> sub2 e (w::acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let max =
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [w] -> w | _ -> Max acc)
		| Max ws' :: ws -> sub (ws' @ acc) ws
		| w :: ws -> sub (w :: acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let eval_w solver =
	let rec sub w =
		match w with
		| BVar(_,_) -> w
		| Smt e -> Smt (solver#get_value e)
		| Prod ws -> prod (List.map sub ws)
		| Sum ws -> sum (List.map sub ws)
		| Max ws -> max (remdups (List.map sub ws))
		| Cond(e,w1,w2) -> (
				match solver#get_value e with
				| LB b -> sub (if b then w1 else w2)
				| e' -> Cond(e', sub w1, sub w2)
			)
	in
	fun w -> sub w

let eval_vec solver = Array.map (eval_w solver)

let eq_0_w =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e =^ LI 0
		| Prod ws -> smt_exists sub ws
		| Sum ws -> smt_for_all sub ws (* cancellation is not considered *)
		| Max ws -> smt_for_all sub ws (* incomplete *)
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let eq_1_w =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e =^ LI 1
		| Prod ws -> smt_for_all sub ws (* division is not considered *)
		| Sum ws -> sub_sum ws
		| Max ws -> smt_for_all sub ws (* incomplete *)
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all eq_0_w ws) |^ (eq_0_w w &^ sub_sum ws)
	in sub

let ge_0_w =
	let rec sub w =
		match w with
		| BVar(_,Pos) | BVar(_,Bool) -> LB true
		| BVar(_,Neg) -> LB false
		| BVar(_,Full) -> LB false (* incomplete *)
		| Smt e -> e >=^ LI 0
		| Prod ws -> LB true (* don't support negative in products *)
		| Sum ws -> smt_for_all sub ws (* cancellation is not considered *)
		| Max ws -> smt_exists sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let ge_1_w =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e >=^ LI 1
		| Prod ws -> smt_for_all sub ws
		| Sum ws -> sub_sum ws
		| Max ws -> smt_exists sub ws
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all ge_0_w ws) |^ (ge_0_w w &^ sub_sum ws)
	in sub

let const_on_w x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB (x <> v)
		| Smt e -> LB true
		| Prod ws -> smt_for_all sub ws |^ smt_exists eq_0_w ws
		| Sum ws -> smt_for_all sub ws
		| Max ws -> smt_for_all sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let is_var_w x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB(x = v)
		| Smt e -> LB false
		| Prod ws -> sub_prod ws
		| Sum ws -> sub_sum ws
		| Max ws -> sub_max ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_prod ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all eq_1_w ws) |^ (eq_1_w w &^ sub_prod ws)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all eq_0_w ws) |^ (eq_0_w w &^ sub_sum ws)
	and sub_max ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all eq_0_w ws) |^ (eq_0_w w &^ sub_max ws)
	in sub

let weak_simple_on_w x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB(x = v)
		| Smt e -> LB false
		| Prod ws -> sub_prod ws
		| Sum ws -> sub_sum ws
		| Max ws -> smt_exists sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_prod ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all ge_1_w ws) |^ (ge_1_w w &^ sub_prod ws)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_for_all ge_0_w ws) |^ (ge_0_w w &^ sub_sum ws)
	in sub

let put_w var : 'a t -> #printer -> unit =
	let paren l l' m = if l <= l' then m else putc '(' << m << putc ')' in
	let rec sub l w =
		match w with
		| BVar(v,_) -> var v
		| Smt (LI i) -> put_int i
		| Smt e -> put_exp e
		| Prod ws ->
			if List.exists (fun w -> w = Smt (LI 0)) ws then putc '0'
			else (
				match List.filter (fun w -> w <> Smt (LI 1)) ws with
				| [w] -> sub l w
				| ws -> paren l 2 (put_list (sub 2) (puts " * ") (putc '1') ws)
			)
		| Sum ws -> (
			match List.filter (fun w -> w <> Smt (LI 0)) ws with
			| [w] -> sub l w
			| ws -> paren l 1 (put_list (sub 1) (puts " + ") (putc '0') ws)
		)
		| Max ws -> puts "max{" << put_list (sub 0) (puts ", ") (puts "-oo") ws << puts "}"
		| Cond(e,w1,w2) -> paren l 0 (put_exp e << puts " ? " << sub 1 w1 << puts " : " << sub 0 w2)
	in
	fun w os -> (sub 0 w) os

let put_vec var wa = puts "(" << put_list (put_w var) (puts ", ") (puts "-") (Array.to_list wa) << puts ")"

let put_range s = puts (
	match s with Full -> "full" | Pos -> "pos" | Neg -> "neg" | Bool -> "bool"
)

let put_var (v,i) = putc '<' << puts v << putc '_' << put_int (i+1) << putc '>'

let put_svar (v,i,s) = putc '<' << puts v << putc '_' << put_int (i+1) << putc ':' << put_range s << putc '>'

let put_cws var cws =
	puts "{ " <<
	put_list (fun (c,w) -> put_exp c << puts "\t:--> " << put_w var w) (puts "\n	") (puts "??") cws <<
	puts "}"

(* A polynomial is represented by a map. *)
module Poly = Map.Make(LexList(Hashed (struct type t = string * int * range end)))

let zero_poly = Poly.empty

let poly_coeff vs p =
	match Poly.find_opt vs p with
	| Some e -> e
	| _ -> LI 0

let put_monom vs e os = put_exp e os; List.iter (fun v -> puts "*" os; put_svar v os) vs

let put_poly p os = puts "SUM {" os; Poly.iter (fun vs e -> put_monom vs e os; os#puts ", ") p; putc '}' os

let refer_poly solver = Poly.map solver#refer_base

let var_poly v i r = Poly.singleton [(v,i,r)] (LI 1)

let const_poly = Poly.singleton []

let add_poly = Poly.union (fun vs e1 e2 -> Some (e1 +^ e2))

let sum_poly = List.fold_left add_poly Poly.empty

(* Product of sorted variable lists. Boolean variables are idempotent. *)
let mul_vars =
	let rec sub ret vs1 vs2 =
		match vs1,vs2 with
		| [], _ -> ret @ vs2
		| _, [] -> ret @ vs1
		| (_,_,r1 as v1)::vs1', v2::vs2' ->
			let c = compare v1 v2 in
			if c = 0 then sub (v1::(if r1 = Bool then ret else v2::ret)) vs1' vs2'
			else if c < 0 then sub (v1::ret) vs1' vs2
			else sub (v2::ret) vs1 vs2'
	in sub []

let add_monom_poly vs1 e1 = Poly.update vs1 (function None -> Some e1 | Some e2 -> Some (e1 +^ e2))

let mul_poly p1 p2 =
	let folder1 vs1 e1 acc =
		let folder2 vs2 e2 acc = add_monom_poly (mul_vars vs1 vs2) (e1 *^ e2) acc in
		Poly.fold folder2 p2 acc
	in
	Poly.fold folder1 p1 Poly.empty

let prod_poly = List.fold_left mul_poly (Poly.singleton [] (LI 1))

let eq_0_poly p =
	let folder vs1 e1 acc = acc &^ (e1 =^ LI 0) in
	Poly.fold folder p (LB true)

let ge_monom =
	let rec sub flag vs = 
		match vs with
		| [] -> if flag then (>=^) else (<=^)
		| (v,i,s) :: vs ->
			match s with
			| Full -> (=^)
			| Pos | Bool -> sub flag vs
			| Neg -> sub (not flag) vs
	in sub true

let ge_poly_merged =
	let merger vs e1opt e2opt = Some(
		match e1opt, e2opt with
		| Some e1, Some e2 -> ge_monom vs e1 e2
		| Some e1, None    -> ge_monom vs e1 (LI 0)
		| None   , Some e2 -> ge_monom vs (LI 0) e2
		)
	in
	fun p1 p2 -> Poly.(bindings (merge merger p1 p2))

let ge_poly p1 p2 = smt_for_all (fun (vs,e) -> e) (ge_poly_merged p1 p2)

let order_poly solver p1 p2 =
	let pre = solver#refer Smt.Bool (smt_for_all (fun (vs,e) -> if vs = [] then LB true else e) (ge_poly_merged p1 p2)) in
	let e1 = poly_coeff [] p1 in
	let e2 = poly_coeff [] p2 in
	let ge = (e1 >=^ e2) &^ pre in
	let gt = (e1 >^ e2) &^ pre in
	(ge, gt)

(* Max Polynomials *)
type mpoly = exp Poly.t list

let bottom_mpoly = []

let zero_mpoly = [zero_poly]

let put_mpoly mp = puts "max {" << put_list put_poly (puts ", ") nop mp << puts "}"

let refer_mpoly solver = List.map (refer_poly solver)

let var_mpoly v i r = [var_poly v i r]

let const_mpoly e = [const_poly e]

let max_mpoly = List.concat

let sum_mpoly mps : mpoly = List.map sum_poly (list_product mps)

let prod_mpoly mps = List.map prod_poly (list_product mps)

let eq_0_mpoly = smt_for_all eq_0_poly

let ge_mpoly mp1 mp2 =
	smt_for_all (fun p2 -> smt_exists (fun p1 -> ge_poly p1 p2) mp1) mp2

let order_mpoly solver mp1 mp2 =
	let (ge,gt) =
		List.fold_left (fun (all_ge,all_gt) p2 ->
			let (ge,gt) =
				List.fold_left (fun (ex_ge,ex_gt) p1 ->
					let (ge,gt) = order_poly solver p1 p2 in
					(ex_ge |^ ge, ex_gt |^ gt)
				)
				(LB false, LB false)
				mp1
			in
			(all_ge &^ ge, all_gt &^ gt)
		)
		(LB true, LB true)
		mp2
	in
	(ge,gt)

(* Conditioned Max Polynomials *)
type cmpoly = (exp * mpoly) list

let bottom_cmpoly = [(LB true, bottom_mpoly)]

let zero_cmpoly = [(LB true, zero_mpoly)]

let refer_cmpoly solver = List.map (fun (c,mp) -> (solver#refer Smt.Bool c, refer_mpoly solver mp))

let var_cmpoly v i r = [(LB true, var_mpoly v i r)]

let const_cmpoly e = [(LB true, const_mpoly e)]

let cmps_op =
	let sub (c1,mp1) (c2,mps) = match c1 &^ c2 with LB false -> None | c -> Some (c, mp1 :: mps) in
	fun f cmps -> List.map (fun (c,mps) -> (c, f mps)) (list_product_fold_filter sub cmps [(LB true,[])])

let sum_cmpoly = cmps_op sum_mpoly

let prod_cmpoly = cmps_op prod_mpoly

let max_cmpoly = cmps_op max_mpoly

let cond_cmpoly c cmp1 cmp2 =
	let sub1 (d,mp) = match c &^ d with LB false -> None | d -> Some (d,mp) in
	let nc = smt_not c in
	let sub2 (d,mp) = match nc &^ d with LB false -> None | d -> Some (d,mp) in
	List.filter_map sub1 cmp1 @ List.filter_map sub2 cmp2

let eq_0_cmpoly = smt_for_all (fun (c,mp) -> c =>^ eq_0_mpoly mp) 

let ge_cmpoly cmp1 cmp2 =
	smt_conjunction (list_prod (fun(c1,mp1) (c2,mp2) -> (c1 &^ c2) =>^ ge_mpoly mp1 mp2) cmp1 cmp2)

let order_cmpoly solver cmp1 cmp2 =
	let ords = list_prod_filter (fun (c1,mp1) (c2,mp2) ->
			match c1 &^ c2 with
			| LB false -> None
			| c ->
				let (ge,gt) = order_mpoly solver mp1 mp2 in Some (c =>^ ge, c =>^ gt)
		) cmp1 cmp2
	in
	let folder (ge,gt) (all_ge,all_gt) = (ge &^ all_ge, gt &^ all_gt) in
	let (ge,gt) = List.fold_left folder (LB true, LB true) ords in
	(ge,gt)

(* Vectors *)
let zero_vec dim = Array.make dim (zero_cmpoly)

let refer_vec solver = Array.map (refer_cmpoly solver)

let smult e = Array.map (fun cmp -> prod_cmpoly [const_cmpoly e; cmp])

let add_vec v1 v2 = Array.mapi (fun i w1 -> sum_cmpoly [w1; v2.(i)]) v1

let order_vec param solver =
	let tmps = param.w_templates in
	let dim = Array.length tmps in
	if dim = 0 then fun _ _ -> weakly_ordered
	else fun v1 v2 ->
		Delay (fun solver ->
			let (_,ge,gt) =
				Array.fold_left (fun (i,ge_rest,gt_rest) (_,mode,_) ->
				let w1 = v1.(i) in
				let w2 = v2.(i) in
				match mode with
				| O_strict ->
					let (ge,gt) = order_cmpoly solver w1 w2 in
					(i+1, ge_rest &^ ge, gt_rest &^ gt)
				| O_weak ->
					(i+1, ge_rest &^ ge_cmpoly w1 w2, gt_rest)
				| O_strict_or_bottom ->
					let (ge,gt) = order_cmpoly solver w1 w2 in
					(i+1, ge_rest &^ ge, gt_rest &^ (gt |^ eq_0_cmpoly w2))
				) (0, LB true, LB true) tmps
			in Cons(ge,gt)
		)

type pos_info = {
	const : exp;
	just : exp;
	weak_simple : exp;
}
type sym_info = {
	encodings : (int * int) t array;
	pos_info : pos_info array;
}

exception Continue

let maxsum_heuristic (trs:Trs.trs) (dg:Dp.dg) =
object (x)
	val sym_table : (string, bool) Hashtbl.t = Hashtbl.create 64
	val mutable initialized = false
	method sym_mode f = if not initialized then x#init; x#get_max f
	method private set_max f =
		Hashtbl.replace sym_table f true
	method private get_max f =
		try Hashtbl.find sym_table f
		with Not_found -> false

	method private init =
		let rec annotate_vs (Node(f,ss)) =
			let args = List.map annotate_vs ss in
			let argvss = List.map get_weight args in
			let vs =
				if f#is_var then [Mset.singleton f#name]
				else if x#get_max f#name then
					List.concat argvss
				else
					List.map (List.fold_left Mset.union Mset.empty) (list_product argvss)
			in
			WT(f,args,vs)
		in
		let vcond svss tvss =
			List.for_all (fun tvs -> List.exists (Mset.subseteq tvs) svss) tvss
		in
		let rec sub (WT(f,ss,svss) as s) (WT(g,ts,tvss)) =
			List.iter (sub s) ts;
			if not (vcond svss tvss) && (not (x#get_max g#name) || (debug (puts "ok it happens..." << endl); false))
			then (x#set_max g#name; raise Continue);
		in
		let annotate_sub i lr =
			sub (annotate_vs lr#l) (annotate_vs lr#r);
		in
		let rec loop () =
			try
				trs#iter_rules annotate_sub;
				dg#iter_dps annotate_sub;
			with Continue -> loop ()
		in
		loop ();
		initialized <- true;
end;;

class interpreter p =
	let dim = Array.length p.w_templates in
	let range_of_coord i = let (r,_,_) = p.w_templates.(i) in r in
	let to_dim = int_list 0 (dim-1) in
	let put_arg =
		if dim = 1 then fun (k,_) -> puts "x" << put_int (k+1)
		else fun (k,i) -> puts "x" << put_int (k+1) << putc '_' << put_int (i+1)
	in
	object (x)
		val table = Hashtbl.create 64
		method init : 't. (#context as 't) -> Trs.trs -> Dp.dg -> unit = fun solver trs dg ->
			let heu = maxsum_heuristic trs dg in
			let iterer f =
				let n = f#arity in
				let to_n = int_list 0 (n-1) in
				let rec sub k t =
						match t with
						| Strategy.Var Bool ->
							let v = solver#temp_variable Smt.Bool in
							Smt(smt_if v (LI 1) (LI 0))
						| Strategy.Var r ->
							let v = solver#temp_variable_base in
							if r = Pos then solver#add_assertion (v >=^ LI 0)
							else if r = Neg then solver#add_assertion (v <=^ LI 0);
							Smt v
						| Strategy.Choice [t1;t2] ->
							let w1 = sub k t1 in
							let w2 = sub k t2 in
							let c = solver#temp_variable Smt.Bool in
							( match w1, w2 with
								| Smt e1, Smt e2 -> Smt(smt_if c e1 e2)
								| _ -> Cond(c,w1,w2)
							)
						| Strategy.Arg(i,j) -> BVar(((if i >= 0 then i else k), j), range_of_coord j)
						| Strategy.Const n -> Smt(LI n)
						| Strategy.Prod ts -> prod(List.map (sub k) ts)
						| Strategy.Sum ts -> sum(List.map (sub k) ts)
						| Strategy.Max ts -> max(List.map (sub k) ts)
						| Strategy.ProdArgs t -> prod(List.map (fun l -> sub l t) to_n)
						| Strategy.SumArgs t -> sum(List.map (fun l -> sub l t) to_n)
						| Strategy.MaxArgs t -> max(List.map (fun l -> sub l t) to_n)
						| Strategy.Heuristic1(t1,t2) -> sub k (if heu#sym_mode f#name then t2 else t1)
						| Strategy.ArityChoice fn -> sub k (fn n)
				in
				let vec = Array.map (fun (r,o,t) -> sub 0 t) p.w_templates in
				Hashtbl.add table f#name {
					encodings = vec;
					pos_info = Array.of_list (
						List.map (fun k ->
							{
								const = smt_for_all (fun i ->
									smt_for_all (fun j -> const_on_w (k,i) vec.(j)) to_dim
								) to_dim;
								just = smt_for_all (fun i -> is_var_w (k,i) vec.(i)) to_dim;
								weak_simple = smt_for_all (fun i -> weak_simple_on_w (k,i) vec.(i)) to_dim;
							}
						) (int_list 0 (f#arity - 1))
					);
				}
			in
			trs#iter_funs iterer;
			debug (fun os ->
				os#endl; os#puts "Weight template:"; os#endl;
				trs#iter_funs (fun f ->
					x#output_sym_template f os;
					endl os
				)
			)

		method private find : 'f. (#sym as 'f) -> _ =
			fun f -> Hashtbl.find table f#name

		method constant_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) is constant *)
			fun f k -> (x#find f).pos_info.(k-1).const

		method collapses_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) = x_k *)
			fun f k -> (x#find f).pos_info.(k-1).just

		method weak_simple_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) >= x_k *)
			fun f k -> (x#find f).pos_info.(k-1).weak_simple

		method private encode_sym : 'f. (#sym as 'f) -> _ =
			fun f -> (x#find f).encodings

		method interpret : 'f. (#sym as 'f) -> cmpoly array list -> cmpoly array =
			fun f vs ->
			let subst = Array.of_list vs in
			let rec sub w =
				match w with
				| Smt e -> const_cmpoly e
				| BVar((k,i),s) -> subst.(k).(i)
				| Max ws -> max_cmpoly (List.map sub ws)
				| Sum ws -> sum_cmpoly (List.map sub ws)
				| Prod ws -> prod_cmpoly (List.map sub ws)
				| Cond(e,w1,w2) -> cond_cmpoly e (sub w1) (sub w2)
			in
			if f#is_var then Array.init dim (fun i -> var_cmpoly f#name i (range_of_coord i))
			else Array.map sub (x#encode_sym f)

		method annotate : 't 'f. (#context as 't) -> (#sym as 'f) term -> ('f, cmpoly array) wterm =
			fun solver (Node(f,ss)) ->
			let ts = List.map (x#annotate solver) ss in
			let vec = x#interpret f (List.map get_weight ts) in
			WT(f, ts, refer_vec solver vec)

		method output_sym : 't 'f 'o. (#solver as 't) -> (#Trs.sym_detailed as 'f) -> (#printer as 'o) -> unit =
			fun solver f os -> put_vec put_arg (eval_vec solver (x#encode_sym f)) os;

		method output_sym_template : 'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
			fun f -> f#output << puts ": " << put_vec put_arg (x#encode_sym f)
	end



