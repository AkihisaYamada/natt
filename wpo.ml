open Util
open Term
open Trs
open Dp
open Smt
open Preorder
open Params
open Io

exception Continue

let k_comb x _ = x
let supply_index v i = v ^ "_" ^ string_of_int i


(* delete common elements from ss and ts *)
let delete_common =
	let rec sub ss1 ss ts =
		match ss with
		| [] -> ss1, ts
		| s :: ss ->
			match delete_one [] s ts with
			| Some ts -> sub ss1 ss ts
			| None -> sub (s::ss1) ss ts
	in
	sub []

type finfo =
{
	sym : sym;
	symtype : symtype;
	is_associative : bool;
	is_commutative : bool;
	arity : int;
	mutable max : bool;
	mutable maxpol : bool;
	mutable maxfilt_exp : int -> exp;
	mutable status_mode : status_mode;
	mutable argfilt_exp : int -> exp;
	mutable argfilt_list_exp : exp;
	mutable is_const_exp : exp;
	mutable is_quasi_const_exp : exp;
	mutable perm_exp : int -> int -> exp;
	mutable permed_exp : int -> exp;
	mutable mapped_exp : int -> exp;
	mutable mset_status_exp : exp;
	mutable weight_exp : exp;
	mutable subterm_coef_exp : int -> exp;
	mutable subterm_penalty_exp : int -> exp;
	mutable prec_exp : exp;
}
let default_finfo (f:#sym_detailed) =
{
	sym = (f:>sym);
	symtype = f#ty;
	arity = f#arity;
	is_commutative = f#is_commutative;
	is_associative = f#is_associative;
	max = false;
	maxpol = false;
	maxfilt_exp = k_comb (LB false);
	status_mode = S_none;
	argfilt_exp = k_comb Nil;
	argfilt_list_exp = Nil;
	is_const_exp = LB(f#arity = 0);
	is_quasi_const_exp = LB(f#arity = 0);
	perm_exp = k_comb (k_comb (LB false));
	permed_exp = k_comb (LB false);
	mapped_exp = k_comb (LB false);
	mset_status_exp = LB false;
	weight_exp = LI 0;
	subterm_coef_exp = k_comb (LI 1);
	subterm_penalty_exp = k_comb (LI 0);
	prec_exp = LI 0;
}

class processor p (trs : trs) (estimator : Estimator.t) (dg : dg) =

	(* SMT variables *)

	let mcw_v = "w" in
	let usable_v i = "u_" ^ string_of_int i in
	let usable_w_v i = "uw_" ^ string_of_int i in
	let maxcons_v = "maxcons" in

	let usables = ref [] in
	let dplist = ref [] in
	let weight_ty =
		match p.base_ty with
		| TY_int -> Int
		| TY_real -> Real
	in
	let solver =
		let (tool,options) = p.smt_tool in
		create_solver p.peek_to p.peek_in p.peek_out tool options
	in
	let () = solver#set_base_ty weight_ty in
	(* Signature as the set of function symbols with their informations. *)
	let sigma = Hashtbl.create 256 in
	let lookup_name name =
		try Hashtbl.find sigma name with  _ -> raise (Internal name)
	in
	let lookup f = lookup_name f#name in
	let nest_map = ref Mset.empty in
	let nest fname = Mset.count fname !nest_map in

(*** Weights ***)
	let weight finfo = finfo.weight_exp in

	let makebin a b =
		smt_if a (smt_if b (LI 3) (LI 2)) (smt_if b (LI 1) (LI 0))
	in
	let add_number w_mode =
		match w_mode with
		| W_num -> fun v -> solver#new_variable v weight_ty
		| W_bool -> fun v -> PB(solver#new_variable v Bool)
		| W_tri -> fun v ->
			smt_if (solver#new_variable (v ^ "a") Bool)
				(smt_if (solver#new_variable (v ^ "b") Bool) (LI 2) (LI 1))
				(LI 0)
		| W_quad -> fun v ->
			makebin (solver#new_variable (v ^ "a") Bool) (solver#new_variable (v ^ "b") Bool)
		| W_none -> fun _ -> LI 0
	in
	(* Minimum weight *)
	let mcw_val = LI p.mcw_val in
	let mcw =
		match p.mcw_mode with
		| MCW_num	-> EV mcw_v
		| MCW_bool	-> PB(EV mcw_v)
		| MCW_const	-> mcw_val
	in
	(* Matrix interpretations *)
	let to_dim = intlist 1 p.w_dim in
	let makemat =
		if p.w_dim > 1 then
			fun f -> Mat(List.map (fun j -> List.map (fun k -> f j k) to_dim) to_dim)
		else
			fun f -> f 1 1
	in
	let makevec =
		if p.w_dim > 1 then
			fun f -> Vec(List.map f to_dim)
		else
			fun f -> f 1
	in
	let supply_matrix_index =
		if p.w_dim > 1 then
			fun v j k -> supply_index (supply_index v j) k
		else
			fun v _ _ -> v
	in
	(* constant part *)
	let add_weight =
		let bind_lower =
			if p.w_neg then
				if p.w_max = 0 then fun _ _ -> ()
				else fun _ fw -> solver#add_assertion (fw >=^ LI (- p.w_max))
			else fun finfo fw -> solver#add_assertion (fw >=^ if finfo.arity = 0 then mcw else LI 0)
		in
		let bind_upper =
			if p.w_max = 0 then fun _ _ -> ()
			else fun _ fw -> solver#add_assertion (fw <=^ LI p.w_max)
		in
		let sub finfo v i =
			let fw = add_number p.w_mode (v i) in
			bind_lower finfo fw;
			bind_upper finfo fw;
			fw
		in
		fun fname finfo ->
			if not p.ac_w && finfo.is_associative then begin
				finfo.weight_exp <- LI 0
			end else begin
				let v =
					if p.w_dim > 1 then supply_index ("w_" ^ fname)
					else k_comb ("w_" ^ fname)
				in
				finfo.weight_exp <- makevec (sub finfo v);
			end;
	in

	(* Coefficients *)
	let subterm_coef finfo = finfo.subterm_coef_exp in
	let add_subterm_coef fname finfo =
		let sub v j k =
			let coef = add_number p.sc_mode (supply_matrix_index v j k) in
			match p.sc_mode with
			| W_num ->
				if not p.dp && j = 1 && k = 1 then begin
					(* if not in DP mode, assert top left element >= 1 *)
					solver#add_assertion (coef >=^ LI 1);
					if p.sc_max > 0 then
						solver#add_assertion (coef <=^ LI (p.sc_max + 1));
				end else begin
					solver#add_assertion (coef >=^ LI 0);
				if p.sc_max > 0 then
					solver#add_assertion (coef <=^ LI p.sc_max);
				end;
				coef
			| W_none ->
				if j = 1 && k = 1 then LI 1 else LI 0
			| _ ->
				if not p.dp && j = 1 && k = 1 then
				(* if not in DP mode, assert top left element >= 1 *)
					coef +^ LI 1
				else
					coef
		in
		match finfo.symtype with
		| Th "C" ->
			finfo.subterm_coef_exp <- k_comb (makemat (sub ("sc_" ^ fname)));
		| Th "A" | Th "AC" ->
			let coef =
				if not p.dp || p.sc_mode = W_none then
					LI 1
				else
					PB(solver#new_variable ("sc_" ^ fname) Bool)
			in
			finfo.subterm_coef_exp <- k_comb coef
		| _ ->
			let n = finfo.arity in
			let v = (if n > 1 then supply_index else k_comb) ("sc_" ^ fname) in
			let array = Array.make n (LI 0) in
			for i = 1 to n do
				array.(i-1) <- makemat (sub (v i));
			done;
			finfo.subterm_coef_exp <- fun i -> array.(i-1);
	in

	(* Max-polynomial *)
	let max_status finfo = finfo.max in
	let maxfilt finfo = finfo.maxfilt_exp in
	let subterm_penalty finfo = finfo.subterm_penalty_exp in
	let add_subterm_penalty fname finfo =
		if max_status finfo then begin
			let sub v j k =
				let pen = add_number p.sp_mode (supply_matrix_index v j k) in
				if not p.w_neg then solver#add_assertion (pen >=^ LI 0);
				if p.w_max > 0 then solver#add_assertion (pen <=^ LI p.w_max);
				pen
			in
			let use_maxpol () =
				finfo.maxpol <- true;
				debug2 (puts "    using maxpol for " << puts fname << endl);
			in
			match finfo.symtype with
			| Th "C" ->
				if p.Params.max_poly &&
					(p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
				then begin
					finfo.subterm_penalty_exp <- k_comb (makemat (sub ("sp_" ^ fname)));
					finfo.maxfilt_exp <- k_comb (solver#new_variable ("maxfilt_" ^ fname) Bool);
					use_maxpol ();
				end else begin
					finfo.maxpol <- false;
					finfo.maxfilt_exp <- (fun i -> subterm_coef finfo i <>^ LI 0);
				end;
			| Th "A" | Th "AC" ->
				if p.Params.max_poly &&
					(p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
				then begin
					finfo.maxfilt_exp <- k_comb (solver#new_variable ("maxfilt_" ^ fname) Bool);
					use_maxpol ();
				end else begin
					finfo.maxpol <- false;
					finfo.maxfilt_exp <- (fun i -> subterm_coef finfo i <>^ LI 0);
				end;
			| _ ->
				let n = finfo.arity in
				let vsp = (if n > 1 then supply_index else k_comb) ("sp_" ^ fname) in
				let array = Array.make n (LI 0) in
				for i = 1 to n do
					array.(i-1) <- makemat (sub (vsp i));
				done;
				finfo.subterm_penalty_exp <- (fun i -> array.(i-1));
				if p.Params.max_poly &&
					(p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
				then begin
					let vmf = (if n > 1 then supply_index else k_comb) ("maxfilt_" ^ fname) in
					let emf i = EV(vmf i) in
					for i = 1 to n do
						solver#add_variable (vmf i) Bool;
					done;
					use_maxpol ();
					finfo.maxfilt_exp <- emf;
				end else begin
					finfo.maxpol <- false;
					finfo.maxfilt_exp <- (fun i -> subterm_coef finfo i <>^ LI 0);
				end;
		end;
	in

	(* accumulation of coeficient for term variables *)
	let vc_lookup vc vname =
		try Hashtbl.find vc vname with Not_found -> LI 0
	in
	let vc_cond vc1 vc2 =
		let comp vname value e = (vc_lookup vc1 vname >=^ value) &^ e in
		Hashtbl.fold comp vc2 (LB true)
	in
	let vc_eq vc1 vc2 =
		if Hashtbl.length vc1 = Hashtbl.length vc2 then
			let comp vname value e = (vc_lookup vc1 vname =^ value) &^ e in
			Hashtbl.fold comp vc2 (LB true)
		else
			LB false
	in
	let vc_add vc coef vname value =
		Hashtbl.replace vc vname (vc_lookup vc vname +^ (coef *^ value))
	in
	let vc_merge vc1 coef vc2 =
		Hashtbl.iter (vc_add vc1 coef) vc2
	in
	let vc_mul vc coef =
		Hashtbl.iter (fun vname value -> Hashtbl.replace vc vname (coef *^ value)) vc
	in
	let vc_refer context vc =
		Hashtbl.iter (fun vname value -> Hashtbl.replace vc vname (context#refer_base value)) vc
	in

	(* weight order *)
	let weq =
		let pol_eq (vc1,e1) (vc2,e2) = vc_eq vc1 vc2 &^ (e1 =^ e2) in
		let rec sub eq w1 ws2 =
			if eq = LB true then eq
			else
				match ws2 with
				| [] -> eq
				| w2::ws2 -> sub (eq |^ pol_eq w1 w2) w1 ws2
		in
		fun ws1 ws2 ->
			if List.length ws1 = List.length ws2 then
				smt_for_all (fun w1 -> sub (LB false) w1 ws2) ws1
			else
				LB false
	in
	let wo =
		if p.w_mode = W_none then
			fun _ _ -> weakly_ordered
		else
			let polo (vc1,e1) (vc2,e2) =
				smt_if (vc_cond vc1 vc2) (smt_order e1 e2) not_ordered
			in
			let rec sub2 ge gt ws1 w2 =
				if gt = LB true then (gt,gt)
				else
					match ws1 with
					| [] -> (ge,gt)
					| w1::ws1 ->
						let (curr_ge,curr_gt) = split (polo w1 w2) solver in
						sub2 (ge |^ curr_ge) (gt |^ curr_gt) ws1 w2
			in
			let rec sub ge gt ws1 ws2 =
				if ge = LB false then not_ordered
				else
					match ws2 with
					| [] ->
						Cons(ge,gt)
					| w2::ws2 ->
						let (curr_ge,curr_gt) = sub2 (LB false) (LB false) ws1 w2 in
						sub (ge &^ curr_ge) (gt &^ curr_gt) ws1 ws2
			in
			fun ws1 ws2 ->
			match ws1, ws2 with
			| [w1], [w2] -> polo w1 w2
			| _ -> sub (LB true) (LB true) ws1 ws2
	in

(*** Maximum constant ***)
	let maxcons = if p.maxcons then EV(maxcons_v) else LB false in

(*** Precedence ***)
	let pmin = LI 0 in
	let pmax = ref (LI 0) in
	let prec finfo = finfo.prec_exp in
	let add_prec_default fname finfo =
		let fp = solver#new_variable ("p_" ^ fname) weight_ty in
		finfo.prec_exp <- fp;
		solver#add_assertion (pmin <=^ fp);
		solver#add_assertion (fp <=^ !pmax);
	in
	let add_prec_ac =
		if p.ac_mode = AC_S90 then
			fun fname finfo -> finfo.prec_exp <- pmin
		else
			fun fname finfo ->
				if marked_name fname then begin
					(* marked AC symbols have the precedence of unmarked one *)
				end else begin
					add_prec_default fname finfo;
				end;
	in
	let add_prec =
		match p.prec_mode with
		| PREC_none -> fun _ _ -> ()
		| _ -> fun fname finfo ->
			(if finfo.is_associative then add_prec_ac else add_prec_default) fname finfo
	in
	(* Precedence over symbols *)
	let spo =
		match p.prec_mode with
		| PREC_quasi ->
			fun finfo ginfo ->
				let pf = prec finfo in
				let pg = prec ginfo in
				Cons(pf >=^ pg, pf >^ pg)
		| _ ->
			fun finfo ginfo ->
				let pf = prec finfo in
				let pg = prec ginfo in
				if pf = pg then
					weakly_ordered
				else
					Dup(Bool, prec finfo >^ prec ginfo)
	in
	(* Precedence of root symbols *)
	let po =
		if p.prec_mode = PREC_none then
			fun _ _ -> weakly_ordered
		else
			let sub =
				if p.mincons then
					function
					| []	-> fun ginfo -> Cons(pmin =^ prec ginfo, LB false)
					| _		-> fun _ -> not_ordered
				else
					fun _ _ -> not_ordered
			in
			fun (WT((f:#sym),_,_)) (WT((g:#sym),ts,_)) ->
				if f#is_var then
					if g#is_var then Cons(LB(f#equals g), LB false)
					else sub ts (lookup g)
				else if g#is_var then not_ordered
				else spo (lookup f) (lookup g)
	in

(*** Argument filters ***)
	let argfilt finfo = finfo.argfilt_exp in
	let add_argfilt =
		(* argument is filtered iff coef = 0 *)
		if not p.dp || p.sc_mode = W_none then
			fun _ finfo ->
				finfo.argfilt_exp <- k_comb (LB true);
		else if p.sc_mode = W_bool && p.w_dim = 1 && not p.Params.max_poly then
			fun _ finfo ->
				finfo.argfilt_exp <- fun i -> subterm_coef finfo i <>^ LI 0;
		else
			(* give an alias for coef <> 0 *)
			let iterer =
				if p.Params.max_poly then
					fun finfo vf i ->
						solver#add_definition (vf i) Bool
						(	(subterm_coef finfo i <>^ LI 0) |^ 
							if finfo.maxpol then maxfilt finfo i else LB false
						);
				else
					fun finfo vf i ->
						solver#add_definition (vf i) Bool (subterm_coef finfo i <>^ LI 0);
			in
			fun fname finfo ->
				let v = "af_" ^ fname in
				match finfo.symtype with
				| Fun | Th "A" ->
					let vf i = supply_index v i in
					let ef i = EV(vf i) in
					for i = 1 to finfo.arity do
						iterer finfo vf i;
					done;
					finfo.argfilt_exp <- ef;
				| Th "AC" | Th "C" ->
					let vf _ = v in
					let ef _ = EV(v) in
					iterer finfo vf 1;
					finfo.argfilt_exp <- ef;
				| _ -> ()
	in
	(* collapsing argument filters *)
	let argfilt_list finfo = finfo.argfilt_list_exp in
	let add_argfilt_list =
		if p.collapse then
			fun fname finfo to_n ->
				let v = "afl_" ^ fname in
				finfo.argfilt_list_exp <- EV(v);
				solver#add_variable v Bool;
				solver#add_assertion (EV(v) |^ ES1(List.map (argfilt finfo) to_n));
		else
			fun _ finfo _ -> finfo.argfilt_list_exp <- LB true
	in

(*** Usable rules ***)
	let usable =
		if p.dp && dg#minimal && p.usable then
			fun i -> EV(usable_v i)
		else
			fun _ -> LB true
	in
	let usable_w =
		if p.dp && p.usable_w then
			fun i -> EV(usable_w_v i)
		else
			usable
	in
	let rec set_usable filt usable s =
		smt_for_all usable (estimator#find_matchable s) &^ set_usable_inner filt usable s
	and set_usable_inner filt usable (Node(f,ss)) =
		if f#is_var then
			smt_for_all (set_usable_inner filt usable) ss
		else
			let finfo = lookup f in
			let rec sub i ss =
				match ss with
				| [] -> LB true
				| s::ss -> (filt finfo i =>^ set_usable filt usable s) &^ sub (i+1) ss
			in
			sub 1 ss
	in
	let add_usable =
		if not p.dp || not p.usable then
			fun _ -> ()
		else
			fun i ->
				solver#add_variable (usable_v i) Bool;
				if p.usable_w then
					solver#add_variable (usable_w_v i) Bool;
	in

(*** Status ***)
	let perm finfo = finfo.perm_exp in
	(* test if $f$'s $i$th argument has position after permutation *)
	let permed finfo = finfo.permed_exp in
	(* test if $f$ has $k$th argument after permutation *)
	let mapped finfo = finfo.mapped_exp in
	(* multiset status *)
	let mset_status finfo = finfo.mset_status_exp in
	(* lexicographic status *)
	let lex_status finfo = smt_not finfo.mset_status_exp in

	let add_perm =
		let sub_lex =
			let sub_perm fname finfo n =
				match finfo.status_mode with
				| S_empty -> finfo.perm_exp <- (fun _ _ -> LB false)
				| S_none -> finfo.perm_exp <- (fun i k -> LB(i = k) &^ argfilt finfo i)
				| _ ->
					if finfo.status_mode = S_total && n = 1 then begin
						finfo.perm_exp <- k_comb (argfilt finfo);
					end else begin
						let perm_v i k = supply_index (supply_index ("st_" ^ fname) i) k in
						let perm_e i k = EV(perm_v i k) in
						for i = 1 to n do
							for k = 1 to n do
								solver#add_variable (perm_v i k) Bool;
							done;
						done;
						finfo.perm_exp <- perm_e;
					end;
			in
			let sub_permed fname finfo n =
				match finfo.status_mode with
				| S_empty ->
					finfo.permed_exp <- (fun i -> LB false)
				| S_partial ->
					let permed_v i = supply_index ("permed_" ^ fname) i in
					let permed_e i = EV(permed_v i) in
					for i = 1 to n do
						solver#add_variable (permed_v i) Bool;
					done;
					finfo.permed_exp <- permed_e;
				| _ -> finfo.permed_exp <- argfilt finfo;
			in
			let sub_mapped fname finfo n to_n =
				match finfo.status_mode with
				| S_empty -> finfo.mapped_exp <- k_comb (LB false);
				| S_none -> finfo.mapped_exp <- argfilt finfo;
				| _ ->
					if p.dp && (p.sc_mode <> W_none || finfo.status_mode = S_partial) then
						let mapped_v k = supply_index ("mapped_" ^ fname) k in
						let mapped_e k = EV(mapped_v k) in
						for k = 1 to n do
							solver#add_variable (mapped_v k) Bool;
						done;
						solver#add_assertion (OD (List.map mapped_e to_n));
						finfo.mapped_exp <- mapped_e;
					else
						finfo.mapped_exp <- k_comb (LB true)
			in
			fun fname finfo n to_n ->
				sub_perm fname finfo n;
				sub_permed fname finfo n;
				sub_mapped fname finfo n to_n;
				for i = 1 to n do
					let p_i = permed finfo i in
					if p.status_copy then begin
						for j = 1 to n do
							solver#add_assertion (perm finfo i j =>^ p_i);
						done;
						solver#add_assertion (p_i =>^ smt_exists (perm finfo i) to_n);
					end else begin
						let (zero,one) = split (ZeroOne (List.map (perm finfo i) to_n)) solver in
						solver#add_assertion (p_i =>^ one);
						solver#add_assertion (p_i |^ zero);
					end;
					let m_i = mapped finfo i in
					let mapper j = perm finfo j i in
					let (zero,one) = split (ZeroOne (List.map mapper to_n)) solver in
					solver#add_assertion (m_i =>^ one);
					solver#add_assertion (m_i |^ zero);
				done;
		in
		let sub_c =
			let sub_perm finfo =
				finfo.perm_exp <-
				match finfo.status_mode with
				| S_empty -> k_comb (k_comb (LB false));
				| S_partial -> fun i j -> if i = j then permed finfo i else LB false;
				| _ -> fun i j -> if i = j then argfilt finfo i else LB false;
			in
			let sub_permed fname finfo =
				match finfo.status_mode with
				| S_empty -> finfo.permed_exp <- k_comb (LB false);
				| S_partial ->
					let permed_v = "permed_" ^ fname in
					let permed_e _ = EV(permed_v) in
					solver#add_variable permed_v Bool;
					finfo.permed_exp <- permed_e;
				| _ ->
					finfo.permed_exp <- finfo.argfilt_exp
			in
			fun fname finfo ->
				sub_perm finfo;
				sub_permed fname finfo;
				finfo.mapped_exp <- finfo.permed_exp;
		in
		fun fname finfo to_n ->
			finfo.status_mode <-
				(if p.status_nest > 0 && nest fname > p.status_nest then S_empty
				 else p.Params.status_mode);
			match finfo.symtype with
			| Th th ->
				if (p.max_mode <> MAX_all || p.sp_mode <> W_none) &&
					(th = "A" || th = "AC") &&
					max_status finfo
				then begin
					(* in this case, we cannot ensure monotonicity... *)
					finfo.status_mode <- S_empty;
				end;
				if th = "C" || th = "AC" then begin
					sub_c fname finfo;
				end else begin
					sub_lex fname finfo finfo.arity to_n;
				end;
			| _ -> sub_lex fname finfo finfo.arity to_n;
	in

	let add_mset_status =
		let sub =
			if not p.ext_mset then
				fun _ -> LB false
			else if p.ext_lex then
				fun fname -> solver#new_variable ("mset_" ^ fname) Bool
			else
				fun _ -> LB true
		in
		fun fname finfo ->
			match finfo.symtype with
			| Th "C"
			| Th "AC" -> finfo.mset_status_exp <- LB true;
			| _ -> if finfo.arity > 1 then finfo.mset_status_exp <- sub fname;
	in

(*** Tests for arity ***)
	let is_const finfo = finfo.is_const_exp in
	let is_quasi_const finfo = finfo.is_quasi_const_exp in
	let is_unary =
		if p.dp && p.sc_mode <> W_none then
			fun finfo to_n ->
				argfilt_list finfo &^
				ES1(List.map (argfilt finfo) to_n) &^
				smt_exists (permed finfo) to_n
		else
			fun _ -> function [_] -> LB true | _ -> LB false
	in

(*** preparing for function symbols ***)
	let add_symbol fname finfo =
		let n = finfo.arity in
		let to_n = intlist 1 n in

		add_weight fname finfo;

		add_subterm_coef fname finfo;
		add_subterm_penalty fname finfo;

		add_argfilt fname finfo;
		add_argfilt_list fname finfo to_n;

		add_prec fname finfo;

		add_perm fname finfo to_n;

		(* for status *)
		add_mset_status fname finfo;

		let afl = argfilt_list finfo in
		let fw = weight finfo in
		let fp = prec finfo in

		(* if $\pi(f)$ is collapsing, then $w(f) = 0$ *)
		solver#add_assertion (afl |^ (fw =^ LI 0));

		for i = 1 to n do
			let pi = permed finfo i in
			let coef = subterm_coef finfo i in

			(* collapsing filter *)
			solver#add_assertion (afl |^ (argfilt finfo i =>^ pi));
			solver#add_assertion (afl |^ (pi =>^ (coef =^ LI 1)));

			(* permed position must be a simple position *)
			if p.w_neg then solver#add_assertion (pi =>^ (fw >=^ LI 0));
			solver#add_assertion (smt_not pi |^ (coef >=^ LI 1) |^ maxfilt finfo i);

			if max_status finfo then begin
				let pen = subterm_penalty finfo i in
				if p.w_neg then solver#add_assertion (pi =>^ (pen >=^ LI 0));
				solver#add_assertion (afl |^ (pen =^ LI 0));
			end;
		done;
		if n > 0 && p.dp && p.sc_mode <> W_none &&
			(p.w_neg || p.adm || p.maxcons || p.mincons || p.mcw_val > 0)
		then begin
			let v = "const_" ^ fname in
			solver#add_definition v Bool
				(afl &^ smt_for_all (fun i -> smt_not (argfilt finfo i)) to_n);
			finfo.is_const_exp <- EV(v);
			if finfo.status_mode = S_partial && (p.mincons || p.maxcons) then begin
				let v = "qconst_" ^ fname in
				solver#add_definition v Bool
					(afl &^ smt_for_all (fun i -> smt_not (permed finfo i)) to_n);
				finfo.is_quasi_const_exp <- EV(v);
			end else begin
				finfo.is_quasi_const_exp <- EV(v);
			end;
		end;

		if p.w_neg || p.mcw_val > 0 then
			(* asserting $mcw$ be the minimal weight of constants. *)
			if max_status finfo then
				solver#add_assertion (fw >=^ mcw)
			else
				solver#add_assertion (is_const finfo =>^ (fw >=^ mcw));

		if p.adm then begin
			if max_status finfo then
				for i = 1 to n do
					solver#add_assertion (argfilt finfo i =>^ (subterm_penalty finfo i >^ LI 0));
				done
			else if p.mcw_val = 0 then
				solver#add_assertion (is_const finfo |^ (fw >^ LI 0))
			else begin
				solver#add_assertion (fp <=^ !pmax);
				(* asserting admissibility of weight and precedence. *)
				solver#add_assertion
					(smt_if (is_unary finfo to_n &^ (fw =^ LI 0)) (fp =^ !pmax) (fp <^ !pmax));
			end;
		end else if p.maxcons then begin
			solver#add_assertion (fp <=^ !pmax);
		end;

		let qc = is_quasi_const finfo in
		if p.mincons then begin
			solver#add_assertion (qc =>^ (fp >=^ pmin));
		end;
		if p.maxcons then begin
			(* if maxcons is true, then only quasi-constant can have the maximum precedence *)
			solver#add_assertion (smt_not maxcons |^ qc |^ (fp <^ !pmax));
			if not p.adm then begin
				let strictly_simple =
					if max_status finfo then
						smt_for_all (fun i -> subterm_penalty finfo i >^ LI 0) to_n
					else
						fw >^ LI 0
				in
				solver#add_assertion (smt_not maxcons |^ qc |^ smt_not afl |^ strictly_simple);
			end;
		end;
	in

(* for weight computation *)
	let refer_w =
		if p.refer_w then
			solver#refer_base
		else
			fun x -> x
	in
	let emptytbl = Hashtbl.create 0 in
	let weight_summand fty finfo =
		let rec sub_ac coef vc w i e =
			function
			| [] -> (vc, w +^ coef *^ (e +^ (LI i *^ w)))
			| (vc',e')::vws ->
				vc_merge vc coef vc';
				sub_ac coef vc w (i + 1) (e +^ e') vws
		in
		let rec sub_c coef vc w e =
			function
			| [] -> (vc, w +^ (coef *^ e))
			| (vc',e')::vws	->
				vc_merge vc coef vc';
				sub_c coef vc w (e +^ e') vws
		in
		let rec sub_lex coef i vc e =
			function
			| [] -> (vc,e)
			| (vc',e')::vws	->
				let c = coef i in
				vc_merge vc c vc';
				sub_lex coef (i + 1) vc (e +^ (c *^ e')) vws
		in
		let sub =
			function
			| []	-> (emptytbl, weight finfo)
			| vces	->
				let vc = Hashtbl.create 4 in
				let (vc,e) =
					match fty with
					| Th "AC"
					| Th "A"	-> sub_ac (subterm_coef finfo 1) vc (weight finfo) (-2) (LI 0) vces
					| Th "C"	-> sub_c (subterm_coef finfo 1) vc (weight finfo) (LI 0) vces
					| _			-> sub_lex (subterm_coef finfo) 1 vc (weight finfo) vces
				in
				vc_refer solver vc;
				(vc, refer_w e)
		in
		List.map sub
	in
	let weight_var f argws =
		if argws <> [] then raise (Internal "higher order variable");
		let vc = Hashtbl.create 1 in
		(vc_add vc (LI 1) f#name (LI 1);[(vc,mcw)])
	in
	let weight_max =
		let folder af sp ret (vc,e) =
			if af = LB true then
				(vc, solver#refer_base (sp +^ e))::ret
			else
				let vc' = Hashtbl.copy vc in
				vc_mul vc' (smt_pb af);
				vc_refer solver vc';
				(vc', solver#refer_base (smt_pb af *^ (sp +^ e)))::ret
		in
		let rec sub_fun finfo i ret =
			function
			| []		-> ret
			| ws::wss	->
				sub_fun finfo (i + 1)
				(List.fold_left (folder (maxfilt finfo i) (subterm_penalty finfo i)) ret ws) wss
		in
		let sub_c finfo =
			let af = maxfilt finfo 1 in
			let sp = subterm_penalty finfo 1 in
			let rec sub ret =
				function
				| []		-> ret
				| ws::wss	-> sub (List.fold_left (folder af sp) ret ws) wss
			in
			sub
		in
		let sub_ac finfo =
			let af = maxfilt finfo 1 in
			let rec sub ret =
				function
				| []		-> ret
				| ws::wss	-> sub (List.fold_left (folder af (LI 0)) ret ws) wss
			in
			sub
		in
		match p.max_mode with
		| MAX_none ->
			if p.w_neg then
				fun f argws ->
					if f#is_var then weight_var f argws
					else
						(* make it lower bounded by mcw *)
						let sum = weight_summand f#ty (lookup f) (list_product argws) in
						if argws = [] then sum else (emptytbl,mcw)::sum
			else
				fun f argws ->
					if f#is_var then weight_var f argws
					else weight_summand f#ty (lookup f) (list_product argws)
		| _ ->
			fun f argws ->
				if f#is_var then weight_var f argws
				else
					let finfo = lookup f in
					if max_status finfo then
						let init =
							if finfo.maxpol then
								weight_summand f#ty finfo (list_product argws)
							else if p.w_neg then
								(* make it lower bounded by mcw *)
								[emptytbl,mcw]
							else []
						in
						match f#ty with
						| Th "C" -> sub_c finfo init argws
						| Th "AC" -> sub_ac finfo init argws
						| _ -> sub_fun finfo 1 init argws
					else
						let sum = weight_summand f#ty finfo (list_product argws) in
						if p.w_neg && argws <> [] then
							(* make it lower bounded by mcw *)
							(emptytbl,mcw)::sum
						else sum
	in
	(* annote terms with weights *)
	let rec annote (Node(f,ss)) =
		let ss =
			match f#ty with
			| Th "AC" -> local_flat f ss
			| _ -> ss
		in
		let args = List.map annote ss in
		let argws = List.map get_weight args in
		let ws = weight_max f argws in
		WT(f, args, ws)
	in

(*** argument comparison ***)
	let lexperm_compargs =
		match p.Params.status_mode with
		| S_empty ->
			fun _ _ _ _ _ -> weakly_ordered
		| S_none ->
			if p.dp && p.sc_mode <> W_none then
				if p.prec_mode = PREC_quasi then
					raise (No_support "quasi-precedence + 0-coefficient + no status")
				else
					fun finfo ginfo order ss ts ->
						if finfo == ginfo then
							filtered_lex_extension (permed finfo) order ss ts
						else not_ordered
			else
				(* simple lexicographic extension is used. *)
				fun _ _ -> lex_extension
		| _ ->
			if p.prec_mode = PREC_quasi then
				fun finfo ginfo ->
					if finfo == ginfo then
						permuted_lex_extension (perm finfo) (mapped finfo)
					else
						permuted_lex_extension2 (perm finfo) (perm ginfo) (mapped finfo) (mapped ginfo)
			else
				fun finfo ginfo ->
					if finfo == ginfo then
						permuted_lex_extension (perm finfo) (mapped finfo)
					else
						fun _ _ _ -> not_ordered
	in

	let statused_compargs finfo ginfo order ss ts =
		match ss, ts with
		| [], []	-> weakly_ordered
		| [], _		-> Cons(is_quasi_const ginfo, LB false)
		| _, []		-> Cons(LB true, smt_not (is_quasi_const finfo))
		| _ ->
			Delay
			(fun context ->
				let (lge,lgt) =
					split (lexperm_compargs finfo ginfo order ss ts) context
				in
				let (mge,mgt) =
					split (filtered_mset_extension (permed finfo) (permed ginfo) order ss ts) context
				in
				Cons
				(	(mset_status finfo &^ mset_status ginfo &^ mge) |^
					(lex_status finfo &^ lex_status ginfo &^ lge),
					(mset_status finfo &^ mset_status ginfo &^ mgt) |^
					(lex_status finfo &^ lex_status ginfo &^ lgt)
				)
			)
	in
	(* compargs for normal function symbols *)
	let default_compargs =
		if p.ext_mset then
			if p.ext_lex then
				statused_compargs
			else
				fun finfo ginfo -> filtered_mset_extension (permed finfo) (permed ginfo)
		else if p.ext_lex then
			lexperm_compargs
		else
			fun _ _ _ _ _ -> weakly_ordered
	in

(*** compargs for AC symbols ***)

	(* Korovin & Voronkov's original auxiliary order *)
	let w_top_order (WT(f,_,sw)) (WT(g,_,tw)) =
		if g#is_var then
			compose (wo sw tw) (Cons(LB(f=g), LB false))
		else if f#is_var then
			not_ordered
		else
			compose (wo sw tw) (compose (spo (lookup f) (lookup g)) (Cons(weq sw tw, LB false)))
	in
	(* Corrected KV03 auxiliary order *)
	let w_top_preorder (WT(f,_,sw)) (WT(g,_,tw)) =
		if g#is_var then
			compose (wo sw tw) weakly_ordered
		else if f#is_var then
			not_ordered
		else
			compose (wo sw tw) (spo (lookup f) (lookup g))
	in
	
	let small_head spo hinfo (WT(f,_,_)) =
		if f#is_var then LB false else strictly (spo hinfo (lookup f))
	in
	let no_small_head spo hinfo s = smt_not (small_head spo hinfo s) in
	let delete_variables =
		let rec sub ss1 =
			function
			| []	-> ss1
			| WT(f,_,_) as s :: ss ->
				if f#is_var then sub ss1 ss else sub (s::ss1) ss
		in
		sub []
	in

	let comparg_ac_S90 _ order ss ts =
		let ss, ts = delete_common ss ts in
		mset_extension order ss ts
	in
	let comparg_ac_rec finfo order ss ts =
		let ss, ts = delete_common ss ts in
		let nss = List.length ss in
		let nts = List.length ts in
		(* variables in ss may not contribute to other than length *)
		let ss = delete_variables ss in
		(* for efficiency *)
		let nxs = List.length ss in
		let nys = nts in
		let xa = Array.of_list ss in
		let ya = Array.of_list ts in
		let compa = Array.init nxs
			(fun i -> Array.init nys
				(fun j -> solver#refer (Prod(Bool,Bool)) (order xa.(i) ya.(j)))
			)
		in
		compose
		(
			let ifilter i = no_small_head spo finfo xa.(i-1) in
			let jfilter j = no_small_head spo finfo ya.(j-1) in
			filtered_mset_extension_body ifilter jfilter nxs nys compa
		)
		(
			if nss > nts then
				strictly_ordered
			else if nss < nts then
			 	not_ordered
			else
				let ifilter i = small_head spo finfo xa.(i-1) in
				let jfilter j = small_head spo finfo ya.(j-1) in
				filtered_mset_extension_body ifilter jfilter nxs nys compa
		)
	in
	let comparg_ac_KV03 finfo order ss ts =
		let ss, ts = delete_common ss ts in
		let nss = List.length ss in
		let nts = List.length ts in
		(* variables in ss may not contribute to other than length *)
		let ss = delete_variables ss in
		let nsh = no_small_head spo finfo in
		compose (
			filtered_mset_extension2 nsh nsh
			(if p.ac_mode = AC_KV03 then w_top_order else w_top_preorder) ss ts
		)
		(
			if nss > nts then
				strictly_ordered
			else if nss < nts then
			 	not_ordered
			else
				mset_extension order ss ts
		)
	in
	let comparg_ac =
		match p.ac_mode with
		| AC_S90 -> comparg_ac_S90
		| AC_rec -> comparg_ac_rec
		| _ -> comparg_ac_KV03
	in
	(* For AC-RPO.
	 * $(cw,cs,ts) \in emb_candidates f ss$ indicates that f(ts) is
	 * a strict embedding of \pi(f(ss)) if cs && cw holds, and
	 * \pi(f(ss)) iteself if not cs but cw.
	 *)
	let emb_candidates fname =
		let rec sub precond preargs ret postargs =
			if precond = LB false then ret else
			match postargs with
			| [] ->
				(* the whole argument is \pi(f(ss)) if the precondition holds *)
				(precond, LB false, preargs) :: ret
			| (WT(g,ts,_) as t)::ss ->
				if fname = g#name then
					(* this argument should be flattened *)
					sub precond preargs ret (ts @ ss)
				else (
				let mapper (tcw,tcs,ts') = (tcw,tcs,ts' @ [t]) in
				let ret = List.map mapper ret in
				if g#is_var then
					(* a variable must remain *)
					sub precond (preargs @ [t]) ret ss
				else
					let ginfo = lookup g in
					let p_g = permed ginfo in
					let afl_g = argfilt_list ginfo in
					(* pop-out an argument *)
					let precond = solver#refer Bool precond in
					let ret = sub2 precond preargs ret afl_g p_g 1 ts in
					(* t may remain, only if its root symbol is not collapsed *)
					sub (precond &^ afl_g) (preargs @ [t]) ret ss
			)
		and sub2 precond preargs ret afl_g p_g i =
			function
			| [] -> ret
			| (WT(h,vs,_) as u)::us ->
				(* If u survives after argfilter, then it can pop out.
				   If moreover g survives, then the pop-out is strict embedding.
				 *)
				let ret =
					(precond &^ p_g i, afl_g, preargs @ (if h#name = fname then vs else [u])) :: ret
				in
				sub2 precond preargs ret afl_g p_g (i+1) us
		in
		sub (LB true) [] []
	in

	let rec ac_rpo_compargs fname finfo ss ts order =
		Delay (fun context ->
			let mapper (scw,scs,ss') =
				(context#refer Bool scw, context#refer Bool scs, ss')
			in
			let sss = List.map mapper (emb_candidates fname ss) in
			let tss = List.map mapper (emb_candidates fname ts) in

			let rec step2 ge gt ss' tss =
			match tss with
			| [] ->
				(* ge to all proper embedding is a condition for gt *)
				(ge, ge &^ gt)
			| (tcw,tcs,ts') :: tss ->
				if tcw = LB false then
					(* this is not even a weak embedding, so don't care *)
					step2 ge gt ss' tss
				else if tcs = LB false then
				 	(* this is at best \pi(t), so go real comparison *)
				 	let (ge2,gt2) = split (comparg_ac finfo order ss' ts') context in
				 	let (ge,gt) = (ge &^ (tcw =>^ ge2), gt |^ (tcw =>^ gt2)) in
				 	step2 ge gt ss' tss
				else
					let (ge3,gt3) = split (ac_rpo_compargs fname finfo ss' ts' order) context in
					let (ge,gt) =
						(ge &^ (tcw =>^ smt_if tcs gt3 ge3),
						 gt |^ (tcw =>^ (smt_not tcs &^ gt3)))
					in
					step2 ge gt ss' tss
			in
			let rec step1 ge gt sss =
			match sss with
			| [] ->
				(ge,gt)
			| (scw,scs,ss') :: sss ->
				if scw = LB false then
					(* this is not even a weak embedding, so don't care *)
					step1 ge gt sss
				else if scs = LB false then
				 	(* this is at best only weak embedding, so go to the next step *)
				 	let (ge2,gt2) = step2 (LB true) (LB false) ss' tss in
				 	let (ge,gt) = (ge |^ (scw &^ ge2), gt |^ (scw &^ gt2)) in
				 	step1 ge gt sss
				else
					let (ge3,gt3) = split (ac_rpo_compargs fname finfo ss' ts order) context in
					(* if this is strict embedding, weak order results strict order *)
					step1 (ge |^ (scw &^ ge3)) (gt |^ (scw &^ smt_if scs ge3 gt3)) sss
			in
			let (ge,gt) = step1 (LB false) (LB false) sss in

			Cons(ge,gt);
		)
	in
	let ac_unmark_name name =
		if marked_name name then unmark_name name else name
	in
	let flat_compargs =
		if not p.dp && p.adm then
			fun fname gname finfo order ss ts ->
				if ac_unmark_name fname = ac_unmark_name gname then
					comparg_ac finfo order ss ts
				else
					not_ordered
		else
			fun fname gname finfo order ss ts ->
				let fname = ac_unmark_name fname in
				let gname = ac_unmark_name gname in
				if fname = gname then
					ac_rpo_compargs fname finfo ss ts order
				else not_ordered
	in
	(* compargs for f and g *)
	let compargs =
		fun fname gname finfo ginfo ->
			match finfo.symtype, ginfo.symtype with
			| Fun, Fun	-> default_compargs finfo ginfo
			| Th "C", Th "C"	->
				fun order ss ts ->
					smt_if
						(mapped finfo 1)
						(smt_if (mapped ginfo 1) (mset_extension order ss ts) strictly_ordered)
						(smt_if (mapped ginfo 1) weakly_ordered not_ordered)
			| Th "A", Th "A"
			| Th "AC", Th "AC"	->
				fun order ss ts ->
					smt_if
						(mapped finfo 1)
						(smt_if (mapped ginfo 1) (flat_compargs fname gname finfo order ss ts) strictly_ordered)
						(smt_if (mapped ginfo 1) weakly_ordered not_ordered)
			| _					-> (fun _ _ _ -> not_ordered)
	in

(*** RPO-like recursive checks ***)

	let order_by_some_arg =
		(* returns:
			some_ge <=> $s_i \gsim t$ for some $i \in \sigma(f)$
			some_gt <=> $s_i \gt t$ for some $i \in \sigma(f)$
		*)
		let rec sub i some_ge some_gt order finfo ss t =
			match ss with
			| []	-> Cons(some_ge, some_gt)
			| s::ss	->
				smt_split (order s t)
				(fun curr_ge curr_gt ->
					sub (i+1) 
					(some_ge |^ (permed finfo i &^ curr_ge))
					(some_gt |^ (permed finfo i &^ curr_gt)) order finfo ss t
				)
		in
		if p.Params.status_mode = S_empty then
			fun _ _ _ _ -> Cons(LB false, LB false)
		else if not p.collapse && p.adm then
			fun _ _ _ (WT(g,_,_)) ->
				if g#is_var then
					Cons(LB true, LB true)
				else
					Cons(LB false, LB false)
		else if not p.collapse && p.mcw_val > 0 then
			fun order finfo ss t ->
				match ss with
				| [s] -> order s t
				| _ ->
					if max_status finfo then
						sub 1 (LB false) (LB false) order finfo ss t
					else
						Cons(LB false, LB false)
		else
			sub 1 (LB false) (LB false)
	in
	let order_all_args =
		let rec sub j all_ge all_gt order s ginfo ts =
			match ts with
			| []	-> Cons(all_ge, all_gt)
			| t::ts	->
				smt_split (order s t)
				(fun curr_ge curr_gt ->
					smt_let Bool curr_gt
					(fun curr_gt ->
						sub (j+1)
						(all_ge &^ (permed ginfo j =>^ curr_ge))
						(all_gt &^ (permed ginfo j =>^ curr_gt)) order s ginfo ts
					)
				)
		in
		if p.Params.status_mode = S_empty then
			fun _ _ _ _ -> Cons(LB true, LB true)
		else if not p.collapse && p.adm then
			fun _ _ _ _ -> Cons(LB true, LB true)
		else if not p.collapse && p.mcw_val > 0 then
			fun order s ginfo ts ->
				match ts with
				| [t] -> order s t
				| _ ->
					if max_status ginfo then
						sub 1 (LB true) (LB true) order s ginfo ts
					else
						Cons(LB true, LB true)
		else
			sub 1 (LB true) (LB true)
	in

(*** WPO frame ***)
	let is_mincons =
		if p.mincons then
			fun finfo -> is_quasi_const finfo &^ (prec finfo =^ pmin)
		else
			fun _ -> LB false
	in
	let is_maxcons =
		if p.maxcons then
			fun finfo -> maxcons &^ is_quasi_const finfo &^ (prec finfo =^ !pmax)
		else
			fun _ -> LB false
	in
	let rec var_eq xname (WT(g,ts,_)) =
		if g#is_var then
			LB(xname = g#name)
		else 
			let ginfo = lookup g in
			let rec sub j =
				function
				| [] -> LB true
				| t::ts -> (argfilt ginfo j =>^ var_eq xname t) &^ sub (j+1) ts
			in
			is_mincons ginfo |^ (smt_not (argfilt_list ginfo) &^ Delay(fun _ -> sub 1 ts))
	in
	let rec wpo (WT(f,ss,sw) as s) (WT(g,ts,tw) as t) =
		if ac_eq s t then
			weakly_ordered
		else
			compose (wo sw tw) (wpo2 s t)
	and wpo2 (WT(f,ss,_) as s) (WT(g,ts,_) as t) =
		if f#is_var then
			Cons(var_eq f#name t, LB false)
		else
			let finfo = lookup f in
			try (* for efficiency *)
				if f = g then
					match ss,ts with
					| [s1], [t1] ->
						let fltp = permed finfo 1 in
						smt_split (wpo2 s1 t1) (fun rge rgt -> Cons(fltp =>^ rge, fltp &^ rgt))
					| _ -> raise Continue
				else raise Continue
			with
			| Continue -> 
				smt_split (order_by_some_arg wpo finfo ss t)
				(fun some_ge some_gt ->
					let fl = argfilt_list finfo in
					let nfl = smt_not fl in
					smt_let Bool some_ge
					(fun some_ge ->
						let some_gt = (nfl &^ some_gt) |^ (fl &^ some_ge) in
						if some_gt = LB true then
							strictly_ordered
						else if g#is_var then
							Cons(some_ge |^ is_maxcons finfo, some_gt)
						else
							let ginfo = lookup g in
							smt_split (order_all_args wpo s ginfo ts)
							(fun all_ge all_gt ->
								let gl = argfilt_list ginfo in
								let ngl = smt_not gl in
								if all_gt = LB false then
									Cons(some_ge |^ (ngl &^ all_ge), some_gt)
								else
									smt_split (compose (po s t) (compargs f#name g#name finfo ginfo wpo ss ts))
									(fun rest_ge rest_gt ->
										smt_let Bool all_gt
										(fun all_gt ->
											let cond = fl &^ gl &^ all_gt in 
											Cons
											(
												some_ge |^ (ngl &^ all_ge) |^ (cond &^ rest_ge),
												some_gt |^ (ngl &^ all_gt) |^ (cond &^ rest_gt)
											)
										)
									)
							)
					)
				)
	in
	let frame =
		if p.prec_mode = PREC_none && p.Params.status_mode = S_empty then
			fun (WT(_,_,sw)) (WT(_,_,tw)) -> wo sw tw
		else wpo
	in

(*** Printing proofs ***)
	let zero =
		function
		| LI 0 -> true
		| LR 0.0 -> true
		| Vec u -> Matrix.is_zero_vec (LI 0) u
		| Mat m -> Matrix.is_zero (LI 0) m
		| _ -> false
	in
	let one =
		function
		| LI 1 -> true
		| LR 1.0 -> true
		| Mat m -> Matrix.is_unit (LI 0) (LI 1) m
		| _ -> false
	in
	let status_is_used =
		p.ext_mset && p.ext_lex ||
		p.Params.status_mode <> S_none && p.Params.status_mode <> S_empty ||
		p.collapse
	in
	let weight_is_used = p.w_mode <> W_none in
	let usable_is_used = p.dp && p.usable in
	let prec_is_used = p.prec_mode <> PREC_none in
	let output_proof (pr:#printer) =
		let pr_exp = output_exp pr in
		let pr_perm finfo =
			pr#puts "sigma(";
			finfo.sym#output pr;
			pr#puts ") = ";
			let punct = ref "" in
			let rbr =
				if solver#get_bool (argfilt_list finfo) then
					if solver#get_bool (mset_status finfo) then
						(pr#puts "{"; "}")
					else (pr#puts "["; "]")
				else ""
			in
			let n = finfo.arity in
			for j = 1 to n do
				for i = 1 to n do
					if solver#get_bool (perm finfo i j) then begin
						pr#puts !punct;
						pr#put_int i;
						punct := ",";
					end;
				done;
			done;
			pr#puts rbr;
		in
		let pr_exp_append =
			function
			| Neg exp -> pr#puts " - "; pr_exp exp;
			| exp -> pr#puts " + "; pr_exp exp;
		in
		let pr_interpret finfo =
			pr#puts "I(";
			finfo.sym#output pr;
			pr#puts ") = ";
			let n = finfo.arity in
			let sc =
				if finfo.symtype = Fun then subterm_coef finfo
				else (fun v _ -> v) (subterm_coef finfo 1)
			in
			let init = ref true in
			let pr_sum () =
				for i = 1 to n do
					let coef = solver#get_value (sc i) in
					if not (zero coef) then begin
						let coef =
							match coef with
							| Neg coef -> pr#puts (if !init then "-" else " - "); coef
							| _ -> if not !init then pr#puts " + "; coef
						in
						if not (one coef) then begin
							pr_exp coef;
							pr#puts " * ";
						end;
						pr#puts "x";
						pr#put_int i;
						init := false;
					end;
				done;
				let w = solver#get_value (weight finfo) in
				if !init then begin
					pr_exp w;
				end else if not (zero w) then begin
					pr_exp_append w;
				end;
			in
			if max_status finfo then begin
				let usemax = solver#get_bool (argfilt_list finfo) in
				for i = 1 to n do
					let pen = solver#get_value (subterm_penalty finfo i) in
					if solver#get_bool (maxfilt finfo i) then begin
						if !init then begin
							if usemax then pr#puts "max(";
						end else begin
							pr#puts ", ";
						end;
						pr#puts "x"; pr#put_int i;
						if not (zero pen) then begin
							match pen with
							| Neg pen -> pr#puts " - "; pr_exp pen;
							| _ -> pr#puts " + "; pr_exp pen;
						end;
						init := false;
					end;
				done;
				if !init then begin
					if finfo.maxpol then begin
						pr_sum ();
					end else begin
						pr_exp mcw;
					end;
				end else begin
					if finfo.maxpol then begin
						pr#puts ", ";
						init := true;
						pr_sum ();
					end;
					if p.w_neg then begin
						pr#puts ", ";
						pr_exp mcw;
					end;
					if usemax then begin
						pr#puts ")";
					end;
				end;
			end else if p.w_neg && not (solver#get_bool (is_const finfo)) then begin
				pr#puts "max(";
				pr_sum ();
				pr#puts ", ";
				pr_exp mcw;
				pr#puts ")";
			end else begin
				pr_sum ();
			end
		in
		let pr_symbol fname finfo =
			let flag = ref false in
			if status_is_used then begin
				pr#puts "\t";
				pr_perm finfo;
				flag := true;
			end;
			if weight_is_used then begin
				pr#puts "\t";
				pr_interpret finfo;
				flag := true;
			end;
			if !flag then pr#endl;
		in
		let pr_prec pr =
			let equiv = if p.prec_mode = PREC_quasi then " = " else ", " in
			let rec sub =
				function
				| [] -> ()
				| ((f:#sym),_)::[] ->
					f#output pr;
				| (f,i)::(g,j)::ps ->
					f#output pr;
					pr#puts (if i = j then equiv else " > ");
					sub ((g,j)::ps)
			in
			pr#puts "    PREC: ";
			sub
			(	List.sort
				(fun (_,i) (_,j) -> compare j i)
				(	Hashtbl.fold
					(fun fname finfo ps ->
						if solver#get_bool (argfilt_list finfo) then
							(finfo.sym, smt_eval_float (solver#get_value (prec finfo)))::ps
						else ps
					)
					sigma
					[]
				)
			);
			pr#endl;
		in
		let pr_usable =
			let folder is (i,_) =
				if solver#get_bool (usable i) then i::is else is
			in
			puts "    USABLE RULES: {" <<
			Abbrev.put_ints " " (List.fold_left folder [] !usables) <<
			puts " }" <<
			endl
		in
		let pr_usable_w =
			let folder is (i,_) =
				if solver#get_bool (usable_w i) then i::is else is
			in
			puts "    USABLE RULES(WEIGHT): {" <<
			Abbrev.put_ints " " (List.fold_left folder [] !usables) <<
			puts " }" <<
			endl
		in
		Hashtbl.iter pr_symbol sigma;
		if prec_is_used then pr_prec pr;
		if usable_is_used || params.debug then pr_usable pr;
		if p.dp && p.usable_w && p.w_mode <> W_none then pr_usable_w pr;
		if p.mcw_mode = MCW_num then begin
			pr#puts "    w0 = ";
			pr_exp (solver#get_value mcw);
			pr#endl;
		end;
	in
	(* Print CPF proof *)
	let output_cpf =
		let put_status finfo pr =
			Xml.enter "status" pr;
			let n = finfo.arity in
			for j = 1 to n do
				for i = 1 to n do
					if solver#get_bool (perm finfo i j) then begin
						Xml.enclose_inline "position" (put_int i) pr;
					end;
				done;
			done;
			Xml.leave "status" pr;
		in
		let put_prec finfo =
			Xml.enclose "precedence" (put_int (smt_eval_int (solver#get_value (prec finfo))))
		in
		let pr_precstat pr _ finfo =
			Xml.enclose "precedenceStatusEntry" (
				finfo.sym#output_xml <<
				Xml.enclose_inline "arity" (put_int finfo.arity) <<
				put_prec finfo <<
				put_status finfo
			) pr
		in
		let pr_interpret pr _ finfo =
			Xml.enter "interpret" pr;
			finfo.sym#output_xml pr;
			let n = finfo.arity in
			Xml.enclose_inline "arity" (put_int n) pr;
			let sc =
				if finfo.symtype = Fun then subterm_coef finfo
				else (fun v _ -> v) (subterm_coef finfo 1)
			in
			let put_poly_int i =
				Xml.enclose "polynomial" (
					Xml.enclose "coefficient" (
						Xml.enclose_inline "integer" (
							put_int i
						)
					)
				)
			in
			let put_sum pr =
				Xml.enter "polynomial" pr;
				Xml.enter "sum" pr;
				for i = 1 to n do
					let coef = smt_eval_int (solver#get_value (sc i)) in
					if coef <> 0 then begin
						Xml.enclose "polynomial" (
							Xml.enclose "product" (
								put_poly_int coef <<
								Xml.enclose "polynomial" (
									Xml.enclose_inline "variable" (
										put_int i
									)
								)
							)
						) pr;
					end;
				done;
				put_poly_int (smt_eval_int (solver#get_value (weight finfo))) pr;
				Xml.leave "sum" pr;
				Xml.leave "polynomial" pr;
			in
			if max_status finfo then begin
				let usemax = solver#get_bool (argfilt_list finfo) in
				if usemax then begin
					Xml.enter "polynomial" pr;
					Xml.enter "max" pr;
				end;
				for i = 1 to n do
					let pen = smt_eval_int (solver#get_value (subterm_penalty finfo i)) in
					if solver#get_bool (maxfilt finfo i) then begin
						Xml.enclose "polynomial" (
							Xml.enclose "sum" (
								Xml.enclose "polynomial" (
									Xml.enclose_inline "variable" (put_int i)
								) <<
								put_poly_int pen
							)
						) pr;
					end;
				done;
				if finfo.maxpol then begin
					put_sum pr;
				end else begin
					put_poly_int (smt_eval_int (solver#get_value mcw)) pr;
				end;
				if usemax then begin
					Xml.leave "max" pr;
					Xml.leave "polynomial" pr;
				end;
			end else if p.w_neg && not (solver#get_bool (is_const finfo)) then begin
				Xml.enclose "polynomial" (
					Xml.enclose "max" (
						put_sum <<
						put_poly_int (smt_eval_int (solver#get_value mcw))
					)
				) pr;
			end else
				put_sum pr;
			Xml.leave "interpret" pr;
		in
		fun pr ->
			Xml.enter "orderingConstraintProof" pr;
			if prec_is_used || status_is_used then begin
				Xml.enter "redPair" pr;
				Xml.enter "weightedPathOrder" pr;
				Xml.enter "precedenceStatus" pr;
				Hashtbl.iter (pr_precstat pr) sigma;
				Xml.leave "precedenceStatus" pr;
			end;
			Xml.enter "redPair" pr;
			Xml.enter "interpretation" pr;
			Xml.enclose "type" (
				Xml.enclose "polynomial" (
					Xml.enclose_inline "domain" (Xml.tag "naturals") <<
					Xml.enclose_inline "degree" (puts "1")
				)
			) pr;
			Hashtbl.iter (pr_interpret pr) sigma;
			Xml.leave "interpretation" pr;
			Xml.leave "redPair" pr;
			if prec_is_used || status_is_used then begin
				Xml.leave "weightedPathOrder" pr;
				Xml.leave "redPair" pr;
			end;
			Xml.leave "orderingConstraintProof" pr;
	in
	let put_usables_cpf =
		Xml.enclose "usableRules" (
			Xml.enclose "rules" (fun (pr:#printer) ->
				let iterer (i, (rule:rule)) =
					if solver#get_bool (usable i) then rule#output_xml pr;
				in
				List.iter iterer !usables;
			)
		)
	in


	let putdot pr =
		pr#putc '.';
		pr#flush;
	in

	let gt_v i = "gt#" ^ string_of_int i in
	let ge_v i = "ge#" ^ string_of_int i in
	let gt_r_v i = "gt" ^ string_of_int i in
	let ge_r_v i = "ge" ^ string_of_int i in

object (x)

	val mutable initialized = false
	val mutable use_scope = p.use_scope
	val mutable use_scope_last_size = 0
	val mutable dp_flag_table = Hashtbl.create 256
	val mutable rule_flag_table = Hashtbl.create 256

	method using_usable = p.dp && p.usable

	method init current_usables scc =
		initialized <- true;
		debug (puts " Initializing.");

		if p.use_scope_ratio > 0 then begin
			let rules_size = List.length current_usables in
			use_scope_last_size <- trs#get_size;
			use_scope <-
				(use_scope_last_size - rules_size) * p.use_scope_ratio < rules_size;
		end;
		if use_scope then begin
			debug(puts " `Scope' mode.");
			dplist := dg#get_dps;
			usables := trs#fold_rules (fun i rule rest -> (i,rule)::rest) [];
		end else begin
			dplist := IntSet.fold (fun i dps -> (i, dg#find_dp i) :: dps) scc [];
			usables := List.map (fun i -> (i, trs#find_rule i)) current_usables;
		end;

		(* generating the signature *)
		Hashtbl.clear sigma;
		let iterer f =
			if not f#is_var then Hashtbl.add sigma f#name (default_finfo f);
		in
		trs#iter_syms iterer;

		(* count nesting *)
		if p.max_nest > 0 || p.status_nest > 0 || p.max_poly_nest > 0 then begin
			let rec nest_term (Node(f,ss)) =
				if f#is_var then
					Mset.empty
				else
					Mset.union (Mset.singleton f#name)
						(List.fold_left Mset.join Mset.empty (List.map nest_term ss))
			in
			let nest_rule rule = Mset.join (nest_term rule#l) (nest_term rule#r) in
			let nest_rules =
				fun rules ->
					List.fold_left Mset.join Mset.empty
						(List.map (fun (_,rule) -> nest_rule rule) rules)
			in
			nest_map := Mset.join (nest_rules !usables) (nest_rules !dplist)
		end;

		if p.prec_mode <> PREC_none then
			(* set max precedence *)
			pmax := LI (Hashtbl.length sigma);

		(* choice of max_status *)
		let set_max =
			let set_max_finfo fname finfo =
				not finfo.max &&
				finfo.arity > 1 &&
				(p.max_nest = 0 || nest fname <= p.max_nest) &&
				(
					debug2 (putc ' ' << put_name fname);
					finfo.max <- true;
					true
				)
			in
			function
			| MAX_dup	->
				let rec annote_vs (Node(f,ss)) =
					let args = List.map annote_vs ss in
					let argvss = List.map get_weight args in
					let vs =
						if f#is_var then [Mset.singleton f#name]
						else if (lookup f).max then
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
					if	not (vcond svss tvss) &&
						set_max_finfo g#name (lookup g)
					then raise Continue;
				in
				let annote_sub (_,lr) =
					sub (annote_vs lr#l) (annote_vs lr#r);
				in
				let rec loop rulelist =
					try List.iter annote_sub rulelist with Continue -> loop rulelist
				in
				loop
			| MAX_all ->
				fun _ ->
					Hashtbl.iter (fun fname finfo -> ignore (set_max_finfo fname finfo)) sigma;
			| _	->
				fun _ -> ();
		in

		debug2 (endl << puts "Max symbols: {");
		set_max p.max_mode !usables;
		set_max p.max_mode !dplist;
		debug2 (puts " }" << endl);

		solver#set_logic
		(	"QF_" ^
			(if p.sc_mode = W_num then "N" else "L") ^
			(if weight_ty = Real then "R" else "I") ^
			"A"
		);

		begin
			match p.mcw_mode with
			| MCW_num  -> solver#add_variable mcw_v weight_ty;
			| MCW_bool -> solver#add_variable mcw_v Bool;
			| _ -> ();
		end;
		solver#add_assertion (mcw >=^ mcw_val);

		if p.maxcons then
			solver#add_variable maxcons_v Bool;

		Hashtbl.iter add_symbol sigma;

		if p.prec_mode = PREC_strict then begin
			(* asserting no equivalence in precedence *)
			let rec subsub pf =
				function
				| [] -> ()
				| pg::pgs ->
					solver#add_assertion (smt_not (pf =^ pg));
					subsub pf pgs;
			in
			let rec sub =
				function
				| []		-> ()
				| pf::pfs	-> subsub pf pfs; sub pfs
			in
			sub (Hashtbl.fold (fun _ finfo vs -> prec finfo::vs) sigma [])
		end;

		if p.prec_mode <> PREC_none then begin
			(* special treatment of associative symbols *)
			let iterer fname finfo =
				if finfo.is_associative then begin
					(* marked associative symbols have the precedence of unmarked one *)
					if marked_name fname then begin
						finfo.prec_exp <- (lookup_name (unmark_name fname)).prec_exp;
					end;
				end;
			in
			Hashtbl.iter iterer sigma;
		end;
		List.iter (fun (i,_) -> add_usable i) !usables;

	method private add_rule i =
		if not (Hashtbl.mem rule_flag_table i) then
		try
			Hashtbl.add rule_flag_table i ();
			let rule = trs#find_rule i in
			debug2 (puts "    Initializing rule " << put_int i << endl );
			let (WT(_,_,lw) as la) = annote rule#l in
			let (WT(_,_,rw) as ra) = annote rule#r in
			if p.dp then begin
				if p.usable_w then begin
					solver#add_assertion
						(usable_w i =>^ set_usable argfilt usable_w rule#r);
					solver#add_assertion
						(usable i =>^ set_usable permed usable rule#r);
					let wge, wgt = split (wo lw rw) solver in
					let wge = solver#refer Bool wge in
					solver#add_assertion (usable_w i =>^ wge);
					if wge = LB false then begin
						solver#add_definition (ge_r_v i) Bool (LB false);
						solver#add_definition (gt_r_v i) Bool (LB false);
					end else begin
						let (rge,rgt) = split (wpo2 la ra) solver in
						solver#add_definition (ge_r_v i) Bool (wge &^ rge);
						solver#add_definition (gt_r_v i) Bool (wgt |^ (wge &^ rgt));
					end;
				end else if p.usable then begin
					solver#add_assertion
						(usable i =>^ set_usable argfilt usable rule#r);
					solver#add_assertion 
						(usable i =>^ weakly (frame la ra));
				end else begin
					solver#add_assertion (weakly (frame la ra));
				end;
			end else if p.remove_all then begin
				solver#add_assertion (strictly (frame la ra));
			end else begin
				(* rule removal mode *)
				let (ge,gt) = split (frame la ra) solver in
				solver#add_assertion (usable i =>^ ge);
				solver#add_definition (gt_r_v i) Bool gt;
			end;
		with Inconsistent ->
			debug (puts " inconsistency detected." << endl);

	method private add_dp i =
		if not (Hashtbl.mem dp_flag_table i) then begin
			Hashtbl.add dp_flag_table i ();
			debug2 (puts "    initializing DP #" << put_int i << endl);
			let dp = dg#find_dp i in
			let (ge,gt) = split (frame (annote dp#l) (annote dp#r)) solver in
			solver#add_definition (ge_v i) Bool ge;
			solver#add_definition (gt_v i) Bool gt;
			(* flag usable rules *)
			if p.usable_w then begin
				solver#add_assertion (set_usable_inner argfilt usable_w dp#r);
				solver#add_assertion (set_usable_inner permed usable dp#r);
			end else begin
				solver#add_assertion (set_usable_inner argfilt usable dp#r);
			end;
		end;

	method reset =
		begin
			match p.reset_mode with
			| RESET_reset -> solver#reset;
			| RESET_reboot -> solver#reboot;
		end;
		Hashtbl.clear dp_flag_table;
		Hashtbl.clear rule_flag_table;
		initialized <- false;

	method push current_usables scc =
		if initialized then begin
			if p.use_scope_ratio > 0 then
				let curr_size = trs#get_size in
				if (use_scope_last_size - curr_size) * p.use_scope_ratio > curr_size then
				begin
					x#reset;
					x#init current_usables scc;
				end;
		end else begin
			x#init current_usables scc;
		end;
		List.iter x#add_rule current_usables;
		IntSet.iter x#add_dp scc;
		if use_scope then
			solver#push;

	method pop =
		if use_scope then
			solver#pop
		else
			x#reset;

	method reduce current_usables sccref =
		comment ( puts (name_order p) << putdot );
		try
			x#push current_usables !sccref;
			comment putdot;
			if p.remove_all then begin
				let iterer i =
					solver#add_assertion
					(EV (if (dg#find_dp i)#is_strict then gt_v i else ge_v i));
				in
				IntSet.iter iterer !sccref;
			end else begin
				let folder i ret =
					solver#add_assertion (EV (ge_v i));
					EV (gt_v i) |^ ret
				in
				solver#add_assertion (IntSet.fold folder !sccref (LB false));
			end;
			comment putdot;
			solver#check;
			comment (puts " succeeded." << endl);
			proof output_proof;
			cpf (Xml.enter "acRedPairProc" << output_cpf << Xml.enter "dps" << Xml.enter "rules");
			let folder i ret =
				if solver#get_bool (EV(gt_v i)) then (
					cpf ((dg#find_dp i)#output_xml);
					dg#remove_dp i;
					sccref := IntSet.remove i !sccref;
					i :: ret
				) else ret
			in
			let rem_dps = IntSet.fold folder !sccref [] in
			proof (puts "    Removed DPs:" << Abbrev.put_ints " #" rem_dps << endl);
			cpf (
				Xml.leave "rules" << Xml.leave "dps" <<
				put_usables_cpf <<
				Xml.enclose_inline "acDPTerminationProof" (Xml.tag "acTrivialProc") <<
				Xml.leave "acRedPairProc"
			);
			x#pop;
			true
		with Inconsistent ->
			comment (puts " ");
			x#pop;
			false

	method direct current_usables =
		try
			comment (puts "Direct " << puts (name_order p) << puts " " << putdot);
			x#push current_usables IntSet.empty;

			comment putdot;
			(* usable i should be true until i is removed. *)
			List.iter (fun i -> solver#add_assertion (usable i)) current_usables;

			if p.remove_all then begin
				comment putdot;
				solver#check;
				comment (puts " orients all." << endl);
				trs#iter_rules (fun i _ -> trs#remove_rule i);
			end else begin
				solver#add_assertion (smt_exists (fun i -> EV(gt_r_v i)) current_usables);
				comment putdot;
				solver#check;
				comment (puts " removes:");
				List.iter
				(fun i ->
					if solver#get_bool (EV(gt_r_v i)) then begin
						trs#remove_rule i;
						comment(fun _ -> prerr_string " "; prerr_int i;);
					end;
				) current_usables;
				comment endl;
			end;
			proof output_proof;
			cpf (
				Xml.enclose "ruleRemoval" (
					Xml.enclose "orderingConstraintProof" (
						Xml.enclose "redPair" output_cpf
					) <<
					trs#output_xml <<
					Xml.enclose "trsTerminationProof" (Xml.tag "rIsEmpty")
				)
			);
			x#pop;
			true
		with Inconsistent -> x#pop; false
end;;
