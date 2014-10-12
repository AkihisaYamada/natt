open Util
open Term
open Trs
open Smt
open Preorder
open Params

exception Continue
exception No_support of string

let k_comb x _ = x
let supply_index v i = v ^ "_" ^ string_of_int i

let rec eq (WT(fty,fname,ss,sw)) (WT(gty,gname,ts,tw)) =
	fty = gty &&
	fname = gname && 
	match fty with
	| Th "C" -> eq_mset ss ts
	| Th "AC" -> eq_mset ss ts
	| _ -> List.for_all2 eq ss ts
and delete_one ts1 s =
	function
	| [] -> None
	| t::ts -> if eq s t then Some(ts1@ts) else delete_one (t::ts1) s ts
and eq_mset ss ts =
	match ss with
	| [] -> ts = []
	| s::ss' ->
		match delete_one [] s ts with
		| None -> false
		| Some ts' -> eq_mset ss' ts'


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
	symtype : symtype;
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
let default_finfo symtype arity =
{
	symtype = symtype;
	arity = arity;
	max = false;
	maxpol = false;
	maxfilt_exp = k_comb (LB false);
	status_mode = S_none;
	argfilt_exp = k_comb Nil;
	argfilt_list_exp = Nil;
	is_const_exp = LB(arity = 0);
	is_quasi_const_exp = LB(arity = 0);
	perm_exp = k_comb (k_comb (LB false));
	permed_exp = k_comb (LB false);
	mapped_exp = k_comb (LB false);
	mset_status_exp = LB false;
	weight_exp = LI 0;
	subterm_coef_exp = k_comb (LI 1);
	subterm_penalty_exp = k_comb (LI 0);
	prec_exp = LI 0;
}

(* embeding relation *)
let rec emb_le (Node(fty,fname,ss) as s) (Node(gty,gname,ts) as t) =
	s = t || List.exists (emb_le s) ts || fname = gname && List.for_all2 emb_le ss ts

(* flat top $f$ from list of functions *)
let local_flat fname =
	let rec sub ss =
		function
		| [] -> ss
		| (Node(_,gname,ts) as t)::us ->
			if fname = gname then sub (sub ss ts) us else sub (t::ss) us
	in
	sub []

class processor p (trs:Trs.t) dg =

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
	let lookup fname =
		try Hashtbl.find sigma fname with  _ -> raise (Internal fname)
	in
	let nest_map = ref Mset.empty in
	let nest fname = Mset.count fname !nest_map in

	(*** Argument filters ***)
	let argfilt finfo = finfo.argfilt_exp in
	let argfilt_list finfo = finfo.argfilt_list_exp in

	(*** Usable rules ***)
	let usable =
		if p.remove_all then
			fun _ -> LB true
		else
			fun i -> EV(usable_v i)
	in
	let usable_w =
		if p.usable_w then
			fun i -> EV(usable_w_v i)
		else
			usable
	in

	(*** Weights ***)
	let weight finfo = finfo.weight_exp in

	(* Minimum weight *)
	let mcw_val = LI p.mcw_val in
	let mcw =
		match p.mcw_mode with
		| MCW_num	-> EV mcw_v
		| MCW_bool	-> PB(EV mcw_v)
		| MCW_const	-> mcw_val
	in
	(* test if $f$ is interpreted as max *)
	let max_status finfo = finfo.max in
	let maxfilt finfo = finfo.maxfilt_exp in

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
	let makebin a b =
		smt_if a (smt_if b (LI 3) (LI 2)) (smt_if b (LI 1) (LI 0))
	in
	(* subterm penalty *)
	let subterm_penalty finfo = finfo.subterm_penalty_exp in
	(* subterm coefficient *)
	let subterm_coef finfo = finfo.subterm_coef_exp in
	(* variable coeficient *)
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

	let maxcons = if p.maxcons then EV(maxcons_v) else LB false in

	(*** Precedence ***)
	let pmin = LI 0 in
	let pmax = ref (LI 0) in
	let prec finfo = finfo.prec_exp in
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
			fun (WT(fty,fname,_,_)) (WT(gty,gname,ts,_)) ->
				match fty, gty with
				| Var, Var	-> Cons(LB(fname = gname), LB false)
				| Var, _	-> sub ts (lookup gname)
				| _, Var	-> not_ordered
				| _			-> spo (lookup fname) (lookup gname)
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

	(*** Usable rules ***)
	let rec set_usable filt usable s =
		smt_for_all (fun ri -> usable ri) (trs#find_matchable s) &^ set_usable_inner filt usable s
	and set_usable_inner filt usable (Node(fty,fname,ss)) =
		if fty = Var then
			smt_for_all (set_usable_inner filt usable) ss
		else
			let finfo = lookup fname in
			let rec sub i ss =
				match ss with
				| [] -> LB true
				| s::ss -> (filt finfo i =>^ set_usable filt usable s) &^ sub (i+1) ss
			in
			sub 1 ss
	in
	let add_usable =
		if p.remove_all then
			fun _ -> ()
		else
			fun i ->
				solver#add_variable (usable_v i) Bool;
				if p.usable_w then
					solver#add_variable (usable_w_v i) Bool;
	in

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
				| Fun		->
					let vf i = supply_index v i in
					let ef i = EV(vf i) in
					for i = 1 to finfo.arity do
						iterer finfo vf i;
					done;
					finfo.argfilt_exp <- ef;
				| Th _		->
					let vf _ = v in
					let ef _ = EV(v) in
					iterer finfo vf 1;
					finfo.argfilt_exp <- ef;
				| _			-> ()
	in

	(* collapsing argument filters *)
	let add_argfilt_list =
		if p.collapse then
			fun fname finfo to_n ->
				let v = "afl_" ^ fname in
				finfo.argfilt_list_exp <- EV(v);
				solver#add_variable v Bool;
				solver#add_assertion (EV(v) |^ ES1(List.map (argfilt finfo) to_n));
		else
			fun _ finfo _ ->
				finfo.argfilt_list_exp <- LB true
	in

	let add_number w_mode =
		match w_mode with
		| W_num -> fun v -> solver#new_variable v weight_ty
		| W_bool -> fun v -> PB(solver#new_variable v Bool)
		| W_tri -> fun v -> If(solver#new_variable (v ^ "a") Bool, If(solver#new_variable (v ^ "b") Bool, LI 2, LI 1), LI 0)
		| W_quad -> fun v -> makebin (solver#new_variable (v ^ "a") Bool) (solver#new_variable (v ^ "b") Bool)
		| W_none -> fun _ -> LI 0
	in

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
			if not p.ac_w && finfo.symtype = Th "AC" then begin
				finfo.weight_exp <- LI 0
			end else begin
				let v =
					if p.w_dim > 1 then supply_index ("w_" ^ fname)
					else k_comb ("w_" ^ fname)
				in
				finfo.weight_exp <- makevec (sub finfo v);
			end;
	in

	let add_prec =
		match p.prec_mode with
		| PREC_none -> fun _ _ -> ()
		| _ ->
			fun fname finfo ->
				if p.ac_mode = AC_S90 && finfo.symtype = Th "AC" then begin
					finfo.prec_exp <- pmin;
				end else begin
					let fp = solver#new_variable ("p_" ^ fname) weight_ty in
					finfo.prec_exp <- fp;
					solver#add_assertion (pmin <=^ fp);
					solver#add_assertion (fp <=^ !pmax);
				end;
	in

	let supply_matrix_index =
		if p.w_dim > 1 then
			fun v j k -> supply_index (supply_index v j) k
		else
			fun v _ _ -> v
	in

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
			| _ ->
				if not p.dp && j = 1 && k = 1 then
				(* if not in DP mode, assert top left element >= 1 *)
					coef +^ LI 1
				else
					coef
		in
		match finfo.symtype with
		| Th "C"	->
			finfo.subterm_coef_exp <- k_comb (makemat (sub ("sc_" ^ fname)));
		| Th "AC"	->
			let coef =
				if p.sc_mode = W_none then
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
				debug2 (fun _ -> prerr_string "    using maxpol for "; prerr_endline fname;);
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
					finfo.maxfilt_exp <- (fun i -> argfilt finfo i);
				end;
			| Th "AC" ->
				if p.Params.max_poly &&
					(p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
				then begin
					finfo.maxfilt_exp <- k_comb (solver#new_variable ("maxfilt_" ^ fname) Bool);
					use_maxpol ();
				end else begin
					finfo.maxpol <- false;
					finfo.maxfilt_exp <- (fun i -> argfilt finfo i);
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
					finfo.maxfilt_exp <- (fun i -> argfilt finfo i);
				end;
		end;
	in

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
					let (zero,one) = split (ZeroOne (List.map (fun j -> perm finfo j i) to_n)) solver in
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
				(if p.status_nest > 0 && nest fname > p.status_nest then S_empty else p.Params.status_mode);
			match finfo.symtype with
			| Th "C" -> sub_c fname finfo;
			| Th "AC" ->
				if max_status finfo && (p.max_mode <> MAX_all || p.sp_mode <> W_none) then begin
					(* in this case, we cannot ensure monotonicity... *)
					finfo.status_mode <- S_empty;
				end;
				sub_c fname finfo;
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
			| Th "C" -> finfo.mset_status_exp <- LB true;
			| Th "AC" -> finfo.mset_status_exp <- LB true;
			| _ -> if finfo.arity > 1 then finfo.mset_status_exp <- sub fname;
	in


	(* preparing for function symbols *)
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
				solver#add_assertion (smt_if (is_unary finfo to_n &^ (fw =^ LI 0)) (fp =^ !pmax) (fp <^ !pmax));
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

	(* for weight *)

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
						| Th "AC"	-> sub_ac (subterm_coef finfo 1) vc (weight finfo) (-2) (LI 0) vces
						| Th "C"	-> sub_c (subterm_coef finfo 1) vc (weight finfo) (LI 0) vces
						| _			-> sub_lex (subterm_coef finfo) 1 vc (weight finfo) vces
				in
				vc_refer solver vc;
				(vc, refer_w e)
		in
		List.map sub
	in
	let weight_var fname argws =
		if argws <> [] then raise (Internal "higher order variable");
		let vc = Hashtbl.create 1 in
		(vc_add vc (LI 1) fname (LI 1);[(vc,mcw)])
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
			| ws::wss	-> sub_fun finfo (i + 1) (List.fold_left (folder (maxfilt finfo i) (subterm_penalty finfo i)) ret ws) wss
		in
		let sub_c finfo =
			let af = maxfilt finfo 1 in
			let sp = subterm_penalty finfo 1 in
			let rec sub2 ret =
				function
				| []		-> ret
				| ws::wss	-> sub2 (List.fold_left (folder af sp) ret ws) wss
			in
			sub2
		in
		let sub_ac finfo =
			let af = maxfilt finfo 1 in
			let rec sub2 ret =
				function
				| []		-> ret
				| ws::wss	-> sub2 (List.fold_left (folder af (LI 0)) ret ws) wss
			in
			sub2
		in
		match p.max_mode with
		| MAX_none ->
			if p.w_neg then
				fun fty fname argws ->
					if fty = Var then weight_var fname argws
					else
						(* make it lower bounded by mcw *)
						let sum = weight_summand fty (lookup fname) (list_product argws) in
						if argws = [] then sum else (emptytbl,mcw)::sum
			else
				fun fty fname argws ->
					if fty = Var then weight_var fname argws
					else weight_summand fty (lookup fname) (list_product argws)
		| _ ->
			fun fty fname argws ->
				if fty = Var then
					weight_var fname argws
				else
					let finfo = lookup fname in
					if max_status finfo then
						let init =
							if finfo.maxpol then
								weight_summand fty finfo (list_product argws)
							else if p.w_neg then
								(* make it lower bounded by mcw *)
								[emptytbl,mcw]
							else []
						in
						match fty with
						| Th "C" -> sub_c finfo init argws
						| Th "AC" -> sub_ac finfo init argws
						| _ -> sub_fun finfo 1 init argws
					else
						let sum = weight_summand fty finfo (list_product argws) in
						if p.w_neg && argws <> [] then
							(* make it lower bounded by mcw *)
							(emptytbl,mcw)::sum
						else sum
	in
	let rec annote (Node(fty,fname,ss)) =
		let ss =
			match fty with
			| Th "AC" -> local_flat fname ss
			| _ -> ss
		in
		let args = List.map annote ss in
		let argws = List.map get_weight args in
		let ws = weight_max fty fname argws in
		WT(fty, fname, args, ws)
	in

	let lexperm_extension =
		match p.Params.status_mode with
		| S_empty ->
			fun _ _ _ _ _ -> weakly_ordered
		| S_none ->
			if p.dp && p.sc_mode <> W_none then
				if p.prec_mode = PREC_quasi then
					raise (No_support "quasi-precedence + 0-coefficient + no status")
				else
					fun finfo ginfo ->
						if finfo == ginfo then
							filtered_lex_extension (permed finfo)
						else
							fun _ _ _ -> not_ordered
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

	let statused_extension finfo ginfo order ss ts =
		match ss, ts with
		| [], []	-> weakly_ordered
		| [], _		-> Cons(is_quasi_const ginfo, LB false)
		| _, []		-> Cons(LB true, smt_not (is_quasi_const finfo))
		| _ ->
			Delay
			(fun context ->
				let (lge,lgt) =
					split (lexperm_extension finfo ginfo order ss ts) context
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
	(* extension for normal function symbols *)
	let default_extension =
		if p.ext_mset then
			if p.ext_lex then
				statused_extension
			else
				fun finfo ginfo -> filtered_mset_extension (permed finfo) (permed ginfo)
		else if p.ext_lex then
			lexperm_extension
		else
			fun _ _ _ _ _ -> weakly_ordered
	in
	(* extension for AC symbols *)
	let ac_extension =
		(* Korovin & Voronkov original *)
		let w_top_order (WT(fty,fname,_,sw)) (WT(gty,gname,_,tw)) =
			if gty = Var then
				compose (wo sw tw) (Cons(LB(fname = gname), LB false))
			else if fty = Var then
				not_ordered
			else
				compose (wo sw tw) (compose (spo (lookup fname) (lookup gname)) (Cons(weq sw tw, LB false)))
		in
		let w_top_preorder (WT(fty,fname,_,sw)) (WT(gty,gname,_,tw)) =
			if gty = Var then
				compose (wo sw tw) weakly_ordered
			else if fty = Var then
				not_ordered
			else
				compose (wo sw tw) (spo (lookup fname) (lookup gname))
		in
		let small_head spo hinfo (WT(fty,fname,_,_)) =
			if fty = Var then LB false else strictly (spo hinfo (lookup fname))
		in
		let no_small_head spo hinfo s = smt_not (small_head spo hinfo s) in
		let delete_variables =
			let rec sub ss1 =
				function
				| []	-> ss1
				| WT(fty,fname,_,_) as s :: ss ->
						if fty = Var then
							sub ss1 ss
						else
							sub (s::ss1) ss
			in
			sub []
		in
		let main =
			match p.ac_mode with
			| AC_S90 ->
				fun _ order ss ts ->
					let ss, ts = delete_common ss ts in
					mset_extension order ss ts
			| AC_rec ->
				fun finfo order ss ts ->
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
			| _ ->
				fun finfo order ss ts ->
					let ss, ts = delete_common ss ts in
					let nss = List.length ss in
					let nts = List.length ts in
					(* variables in ss may not contribute to other than length *)
					let ss = delete_variables ss in
					let nsh = no_small_head spo finfo in
					compose
					(
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
		(*
		 * $(cw,cs,ts) \in emb_candidates~f~s$ indicates that $f(ts)$ is an
		 * embedding when $cs \wedge cw$ holds, and is $\pi(f(s))$ when $cw$ holds.
		 *)
		let emb_candidates fname =
			let rec sub ret =
				function
				| [] -> ret
				| t::ss -> sub (sub1 ret t) ss
			and sub1 pre (WT(gty,gname,ts,_) as t) =
				if fname = gname then
					sub pre ts
				else if gty = Var then
					let mapper (tcw,tcs,ts') = (tcw,tcs,t::ts') in
					List.map mapper pre
				else
					let ginfo = lookup gname in
					let p_g = permed ginfo in
					let afl_g = argfilt_list ginfo in
					let mapper (tcw, tcs, ts') = (afl_g &^ tcw, tcs, t::ts') in
					List.map mapper pre @ sub2 pre afl_g p_g 1 ts
			and sub2 pre afl_g p_g i =
				function
				| [] -> []
				| s::ts ->
					let p_gi = p_g i in
					let mapper (tcw,tcs,ts') = (p_gi &^ tcw, afl_g |^ tcs, ts') in
					sub1 (List.map mapper pre) s @ sub2 pre afl_g p_g (i+1) ts
			in
			fun ss -> sub [(LB true, LB false, [])] ss
		in
		if p.adm && not p.dp then
			fun fname gname ->
				if fname = gname then
					main
				else
					fun _ _ _ _ -> not_ordered
		else
			fun fname gname ->
				if fname = gname then
					(fun finfo order ss ts ->
						let ss, ts = delete_common ss ts in
						Delay
						(fun context ->
							let sss = List.map (fun (scw,scs,ss') -> (context#refer Bool scw, context#refer Bool scs, ss')) (emb_candidates fname ss) in
							let tss = emb_candidates fname ts in
							let ge = context#temp_variable Bool in
							let gt = context#temp_variable Bool in
							List.iter
							(fun (tcw,tcs,ts') ->
								context#add_assertion
								(
									(ge &^ tcw) =>^
									smt_exists
									(fun (scw,scs,ss') ->
										let (ge',gt') = split (main finfo order ss' ts') context in
										scw &^ ge' &^ 
										((gt |^ tcs) =>^ (gt' |^ scs))
									) sss
								);
							) tss;
							Cons(ge, ge &^ gt)
						)
					)
				else
					fun _ _ _ _ -> not_ordered
	in
	(* extensions for f and g *)
	let extend =
		fun fname gname finfo ginfo ->
			match finfo.symtype, ginfo.symtype with
			| Fun, Fun			-> default_extension finfo ginfo
			| Th "C", Th "C"	->
				fun order ss ts ->
					smt_if
						(mapped finfo 1)
						(smt_if (mapped ginfo 1) (mset_extension order ss ts) strictly_ordered)
						(smt_if (mapped ginfo 1) weakly_ordered not_ordered)
			| Th "AC", Th "AC"	->
				fun order ss ts ->
					smt_if
						(mapped finfo 1)
						(smt_if (mapped ginfo 1) (ac_extension fname gname finfo order ss ts) strictly_ordered)
						(smt_if (mapped ginfo 1) weakly_ordered not_ordered)
			| _					-> (fun _ _ _ -> not_ordered)
	in

	(* RPO-like subfunctions *)

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
			fun _ _ _ (WT(gty,_,_,_)) ->
				if gty = Var then
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

	(* WPO frame *)
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
	let rec var_eq xname (WT(gty,gname,ts,_)) =
		if gty = Var then
			LB(xname = gname)
		else 
			let ginfo = lookup gname in
			let rec sub j =
				function
				| [] -> LB true
				| t::ts -> (argfilt ginfo j =>^ var_eq xname t) &^ sub (j+1) ts
			in
			is_mincons ginfo |^ (smt_not (argfilt_list ginfo) &^ Delay(fun _ -> sub 1 ts))
	in
	let rec wpo (WT(_,fname,ss,sw) as s) (WT(_,gname,ts,tw) as t) =
		if eq s t then
			weakly_ordered
		else
			compose (wo sw tw) (wpo2 s t)
	and wpo2 (WT(fty,fname,ss,_) as s) (WT(gty,gname,ts,_) as t) =
		if fty = Var then
			Cons(var_eq fname t, LB false)
		else
			let finfo = lookup fname in
			try
				if fname = gname then
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
						else if gty = Var then
							Cons(some_ge |^ is_maxcons finfo, some_gt)
						else
							let ginfo = lookup gname in
							smt_split (order_all_args wpo s ginfo ts)
							(fun all_ge all_gt ->
								let gl = argfilt_list ginfo in
								let ngl = smt_not gl in
								if all_gt = LB false then
									Cons(some_ge |^ (ngl &^ all_ge), some_gt)
								else
									smt_split (compose (po s t) (extend fname gname finfo ginfo wpo ss ts))
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
			fun (WT(_,_,_,sw)) (WT(_,_,_,tw)) -> wo sw tw
		else wpo
	in


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

	(* Print proof *)
	let prerr_proof =
		let prerr_perm fname finfo =
			prerr_string "sigma(";
			prerr_string fname;
			prerr_string ") = ";
			let punct = ref "" in
			let rbr =
				if solver#get_bool (argfilt_list finfo) then
					if solver#get_bool (mset_status finfo) then
						(prerr_string "{";"}")
					else (prerr_string "[";"]")
				else ""
			in
			let n = finfo.arity in
			for j = 1 to n do
				for i = 1 to n do
					if solver#get_bool (perm finfo i j) then begin
						prerr_string !punct;
						punct := ",";
						prerr_int i;
					end;
				done;
			done;
			prerr_string rbr;
		in
		let prerr_interpret =
			let prerr_exp_append =
				function
				| Neg exp -> prerr_string " - "; prerr_exp exp;
				| exp -> prerr_string " + "; prerr_exp exp;
			in
			fun fname finfo ->
				prerr_string "I(";
				prerr_string fname;
				prerr_string ") = ";
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
								| Neg coef -> prerr_string (if !init then "-" else " - "); coef
								| _ -> prerr_string (if !init then "" else " + "); coef
							in
							if not (one coef) then begin
								prerr_exp coef;
								prerr_string " * ";
							end;
							prerr_string "x";
							prerr_int i;
							init := false;
						end;
					done;
					let w = solver#get_value (weight finfo) in
					if !init then
						prerr_exp w
					else if not (zero w) then
						prerr_exp_append w;
				in
				if max_status finfo then begin
					let usemax = solver#get_bool (argfilt_list finfo) in
					for i = 1 to n do
						let pen = solver#get_value (subterm_penalty finfo i) in
						if solver#get_bool (maxfilt finfo i) then begin
							prerr_string (if !init then if usemax then "max(" else "" else ", ");
							prerr_string "x";
							prerr_int i;
							if not (zero pen) then begin
								match pen with
								| Neg pen -> prerr_string " - "; prerr_exp pen;
								| _ -> prerr_string " + "; prerr_exp pen;
							end;
							init := false;
						end;
					done;
					if !init then begin
						if finfo.maxpol then
							pr_sum ()
						else
							prerr_exp mcw
					end else begin
						if finfo.maxpol then begin
							prerr_string ", ";
							init := true;
							pr_sum ();
						end;
						if p.w_neg then begin
							prerr_string ", ";
							prerr_exp mcw;
						end;
						if usemax then prerr_string ")";
					end;
				end else if p.w_neg && not (solver#get_bool (is_const finfo)) then begin
					prerr_string "max(";
					pr_sum ();
					prerr_string ", ";
					prerr_exp mcw;
					prerr_string ")";
				end else
					pr_sum ();
		in
		let prerr_symbol fname finfo =
			let flag = ref false in
			if p.w_mode <> W_none then begin
				prerr_string "\t";
				prerr_interpret fname finfo;
				flag := true;
			end;
			if
				(
					p.ext_mset && p.ext_lex ||
					p.Params.status_mode <> S_none && p.Params.status_mode <> S_empty ||
					p.collapse
				) &&
				finfo.arity <> 0
			then begin
				prerr_string "\t";
				prerr_perm fname finfo;
				flag := true;
			end;
			if !flag then prerr_newline ();
		in
		let prerr_prec =
			if p.prec_mode = PREC_none then
				fun _ -> ()
			else
				fun _ ->
					let equiv = if p.prec_mode = PREC_quasi then " = " else ", " in
					let rec sub =
						function
						| [] -> ()
						| (fname,_)::[] ->
							prerr_string fname;
						| (fname,i)::(gname,j)::ps ->
							prerr_string fname;
							if i = j then prerr_string equiv else prerr_string " > ";
							sub ((gname,j)::ps)
					in
					prerr_string "    PREC: ";
					sub
					(	Sort.list
						(fun (_,i) (_,j) -> i > j)
						(	Hashtbl.fold
							(fun fname finfo ps ->
								if solver#get_bool (argfilt_list finfo) then
									(fname, smt_eval_float (solver#get_value (prec finfo)))::ps
								else ps
							)
							sigma
							[]
						)
					);
					prerr_newline ();
		in
		let prerr_usable =
			if p.usable then
				let folder abbr (i,_) =
					if solver#get_bool (usable i) then
						abbr#add i
					else abbr
				in
				fun () ->
					prerr_string "    USABLE RULES: {";
					(List.fold_left folder (new Abbrev.for_int stderr " ") !usables)#close;
					prerr_endline " }";
			else
				fun () -> ()
		in
		let prerr_usable_w =
			if p.usable_w && p.w_mode <> W_none then
				let folder abbr (i,_) =
					if solver#get_bool (usable_w i) then
						abbr#add i
					else abbr
				in
				fun () ->
					prerr_string "    USABLE RULES(WEIGHT): {";
					(List.fold_left folder (new Abbrev.for_int stderr " ") !usables)#close;
					prerr_endline " }";
			else
				fun () -> ()
		in
		fun () ->
			Hashtbl.iter prerr_symbol sigma;
			prerr_prec ();
			prerr_usable ();
			prerr_usable_w ();
			if p.mcw_mode = MCW_num then begin
				prerr_string "    w0 = ";
				prerr_exp (solver#get_value mcw);
				prerr_newline ();
			end;
	in
	(* Print CPF proof *)
	let output_cpf os =
		let pr = output_string os in
		let pr_status finfo =
			pr "  <status>\n";
			let n = finfo.arity in
			for j = 1 to n do
				for i = 1 to n do
					if solver#get_bool (perm finfo i j) then begin
						pr "   <position>";
						pr (string_of_int i);
						pr "</position>\n";
					end;
				done;
			done;
			pr "  </status>\n";
		in
		let pr_prec finfo =
			pr "  <precedence>";
			pr (string_of_int (smt_eval_int (solver#get_value (prec finfo))));
			pr "</precedence>\n";
		in
		let pr_precstat fname finfo =
			pr " <precedenceStatusEntry>\n";
			pr "  <name>"; pr fname; pr "</name>\n";
			pr "  <arity>"; pr (string_of_int finfo.arity); pr "</arity>\n";
			pr_status finfo;
			pr_prec finfo;
			pr " </precedenceStatusEntry>\n";
		in
		let pr_interpret fname finfo =
			pr "<interpret>\n <name>"; pr fname; pr "</name>\n";
			let n = finfo.arity in
			pr " <arity>";
			pr (string_of_int n);
			pr "</arity>\n ";
			let sc =
				if finfo.symtype = Fun then subterm_coef finfo
				else (fun v _ -> v) (subterm_coef finfo 1)
			in
			let pr_int i =
				pr "<polynomial><coefficient><integer>";
				pr (string_of_int i);
				pr "</integer></coefficient></polynomial>";
			in
			let pr_sum () =
				pr "<polynomial><sum>";
				for i = 1 to n do
					let coef = smt_eval_int (solver#get_value (sc i)) in
					if coef <> 0 then begin
						pr "<polynomial><product>";
						pr_int coef;
						pr "<polynomial><variable>";
						pr (string_of_int i);
						pr "</variable></polynomial>";
						pr "</product></polynomial>";
					end;
				done;
				pr_int (smt_eval_int (solver#get_value (weight finfo)));
				pr "</sum></polynomial>";
			in
			if max_status finfo then begin
				let usemax = solver#get_bool (argfilt_list finfo) in
				if usemax then
					pr "<polynomial><max>";
				for i = 1 to n do
					let pen = smt_eval_int (solver#get_value (subterm_penalty finfo i)) in
					if solver#get_bool (maxfilt finfo i) then begin
						pr "<polynomial><sum><polynomial><variable>";
						pr (string_of_int i);
						pr "</variable></polynomial>";
						pr_int pen;
						pr "</sum></polynomial>";
					end;
				done;
				if finfo.maxpol then
					pr_sum ()
				else
					pr_int (smt_eval_int (solver#get_value mcw));
				if usemax then pr "</max></polynomial>";
			end else if p.w_neg && not (solver#get_bool (is_const finfo)) then begin
				pr "<polynomial><max>";
				pr_sum ();
				pr_int (smt_eval_int (solver#get_value mcw));
				pr "</max></polynomial>";
			end else
				pr_sum ();
			pr "\n</interpret>\n";
		in
		pr "<weightedPathOrder>\n<precedenceStatus>\n";
		Hashtbl.iter pr_precstat sigma;
		pr "\
</precedenceStatus>
<interpretation>
 <type>
  <polynomial>
   <domain><naturals/></domain>
   <degree>1</degree>
  </polynomial>
 </type>
";
		Hashtbl.iter pr_interpret sigma;
		pr "\
</interpretation>
</weightedPathOrder>
";
	in
	let putdot _ =
		prerr_char '.';
		flush stderr;
	in

	let gt_v i = "gt#" ^ string_of_int i in
	let ge_v i = "ge#" ^ string_of_int i in
	let gt_r_v i = "gt" ^ string_of_int i in
	let ge_r_v i = "ge" ^ string_of_int i in

	object (x)

		val mutable initialized = false
		val mutable use_scope = p.use_scope
		val mutable use_scope_last_size = 0

		method init current_usables scc =
			initialized <- true;
			debug (fun _ -> prerr_string " Initializing.";);

			if p.use_scope_ratio > 0 then begin
				let rules_size = List.length current_usables in
				use_scope_last_size <- trs#get_size;
				use_scope <-
					(use_scope_last_size - rules_size) * p.use_scope_ratio < rules_size;
			end;
			if use_scope then begin
				debug(fun _ -> prerr_string " `Scope' mode.");
				dplist := dg#get_dps;
				usables := trs#fold_rules (fun i rule rest -> (i,rule)::rest) [];
			end else begin
				dplist := IntSet.fold (fun i l -> (i, dg#find_dp i) :: l) scc [];
				usables := List.map (fun i -> (i, trs#find_rule i)) current_usables;
			end;

			(* generating the signature *)
			Hashtbl.clear sigma;
			let transform_finfo fname =
				let finfo = trs#find_sym fname in
				match finfo.Trs.arity with
				| Arity n -> default_finfo finfo.Trs.symtype n
				| _ -> raise (No_support "variadic signature")
			in
			let rec sub (Node(fty,fname,ss)) =
				if fty <> Var && not (Hashtbl.mem sigma fname) then
					Hashtbl.replace sigma fname (transform_finfo fname);
				List.iter sub ss;
			in
			List.iter (fun (_,(l,r)) -> sub l; sub r;) !usables;
			let sub_dp (Node(fty,fname,ss)) =
				if not (Hashtbl.mem sigma fname) then
					Hashtbl.add sigma fname (transform_finfo fname);
				List.iter sub ss;
			in
			List.iter (fun (_,(l,r)) -> sub_dp l; sub_dp r;) !dplist;

			trs#iter_eqs (fun _ (l,r) -> sub l; sub r;);

			(* count nesting *)
			if p.max_nest > 0 || p.status_nest > 0 || p.max_poly_nest > 0 then begin
				let rec nest_term (Node(fty,fname,ss)) =
					if fty = Var then
						Mset.empty
					else
						Mset.union (Mset.singleton fname)
							(List.fold_left Mset.join Mset.empty (List.map nest_term ss))
				in
				let nest_rule (l,r) = Mset.join (nest_term l) (nest_term r) in
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
						debug2 (fun _ -> prerr_char ' '; prerr_string fname;);
						finfo.max <- true;
						true
					)
				in
				function
				| MAX_dup	->
					let rec annote_vs (Node(fty,fname,ss)) =
						let args = List.map annote_vs ss in
						let argvss = List.map get_weight args in
						let vs =
							if fty = Var then [Mset.singleton fname]
							else if (lookup fname).max then
								List.concat argvss
							else
								List.map (List.fold_left Mset.union Mset.empty) (list_product argvss)
						in
						WT(fty,fname,args,vs)
					in
					let vcond svss tvss =
						List.for_all (fun tvs -> List.exists (Mset.subseteq tvs) svss) tvss
					in
					let rec sub (WT(fty,fname,ss,svss) as s) (WT(gty,gname,ts,tvss)) =
						List.iter (sub s) ts;
						if	not (vcond svss tvss) &&
							set_max_finfo gname (lookup gname)
						then raise Continue;
					in
					let annote_sub (_, (Node(_,fname,_) as s,t)) =
						sub (annote_vs s) (annote_vs t);
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

			debug2 (fun _ -> prerr_string "\n    Max symbols: {");
			set_max p.max_mode !usables;
			set_max p.max_mode !dplist;
			debug2 (fun _ -> prerr_endline " }");

			solver#set_logic
			(	"QF_" ^
				(if p.sc_mode = W_num then "N" else "L") ^
				(if weight_ty = Real then "R" else "I") ^
				"A"
			);

			(
				match p.mcw_mode with
				| MCW_num ->
					solver#add_variable mcw_v weight_ty;
				| MCW_bool ->
					solver#add_variable mcw_v Bool;
				| _ -> ();
			);
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

			List.iter (fun (i,_) -> add_usable i) !usables;
			try
				debug2 (fun _ -> prerr_string "    Rules: {"; flush stderr;);
				let iterer (i,(Node(_,fname,_) as l,r)) =
					debug2 (fun _ -> prerr_char ' '; prerr_int i; flush stderr;);
					let (WT(_,_,_,lw) as la) = annote l in
					let (WT(_,_,_,rw) as ra) = annote r in

					if p.remove_all then begin
						solver#add_assertion (strictly (frame la ra));
					end else if p.usable_w then begin
						solver#add_assertion (usable_w i =>^ set_usable argfilt usable_w r);
						solver#add_assertion (usable i =>^ set_usable permed usable r);
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
							solver#add_assertion (usable i =>^ set_usable argfilt usable r);
							solver#add_assertion (usable i =>^ weakly (frame la ra));
						end else begin
						(* rule removal mode *)
							let (ge,gt) = split (frame la ra) solver in
						solver#add_assertion (usable i =>^ ge);
							solver#add_definition (gt_r_v i) Bool gt;
						end;
				in
				List.iter iterer !usables;
				debug2 (fun _ -> prerr_endline " }");

				debug2 (fun _ -> prerr_string "    Equations: {");
				let iterer i (l,r) =
					debug2 (fun _ -> prerr_string " e"; prerr_int i; flush stderr;);
					let la = annote l in
					let ra = annote r in
					solver#add_assertion (weakly (frame la ra) &^ weakly (frame ra la));
				in
				trs#iter_eqs iterer;
				debug2 (fun _ -> prerr_endline " }");

				debug2 (fun _ -> prerr_string "    DPs: {"; flush stderr;);
				let iterer i (l,r) =
					debug2 (fun _ -> prerr_string " #"; prerr_int i; flush stderr;);
					let (ge,gt) = split (frame (annote l) (annote r)) solver in
					solver#add_definition (ge_v i) Bool ge;
					solver#add_definition (gt_v i) Bool gt;
				in
				if use_scope then
					dg#iter_dps iterer
				else
					IntSet.iter (fun i -> iterer i (dg#find_dp i)) scc;
				debug2 (fun _ -> prerr_endline " }");
			with Inconsistent ->
				debug2 (fun _ -> prerr_string " ... }");
				debug (fun _ -> prerr_endline " inconsistency detected.");

		method reset =
			begin
				match p.reset_mode with
				| RESET_reset -> solver#reset;
				| RESET_reboot -> solver#reboot;
			end;
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
			if use_scope then
				solver#push;
		method pop =
			if use_scope then
				solver#pop
			else
				x#reset;

		method reduce current_usables sccref =
			comment
			(fun _ ->
				prerr_string (name_order p);
				putdot ();
			);
			try
				x#push current_usables !sccref;
				comment putdot;
				let some_gt =
					IntSet.fold
					(fun i some_gt ->
						solver#add_assertion (EV(ge_v i));
						let (_,t) = dg#find_dp i in
						if p.usable_w then begin
							solver#add_assertion (set_usable_inner argfilt usable_w t);
							solver#add_assertion (set_usable_inner permed usable t);
						end else begin
							solver#add_assertion (set_usable_inner argfilt usable t);
						end;
						EV(gt_v i) |^ some_gt
					) !sccref (LB false)
				in
				solver#add_assertion some_gt;
				comment putdot;
				solver#check;
				comment (fun _ -> prerr_string " removes:");
				IntSet.iter
				(fun i ->
					if solver#get_bool (EV(gt_v i)) then
					begin
						dg#remove_dp i;
						comment(fun _ -> prerr_string " #"; prerr_int i;);
						sccref := IntSet.remove i !sccref;
					end;
				) !sccref;
				comment (fun _ -> prerr_newline ());
				proof (fun _ -> prerr_proof ());
				cpf output_cpf;
				x#pop;
				true
			with Inconsistent ->
				comment (fun _ -> prerr_string " ");
				x#pop;
				false

		method direct current_usables =
			try
				comment
				(fun _ ->
					prerr_string "Direct ";
					prerr_string (name_order p);
					prerr_string " ";
					putdot ();
				);
				x#push current_usables IntSet.empty;

				comment putdot;
				(* usable i should be true until i is removed. *)
				List.iter (fun i -> solver#add_assertion (usable i)) current_usables;

				if p.remove_all then begin
					comment putdot;
					solver#check;
					comment (fun _ -> prerr_endline " orients all.");
					trs#iter_rules (fun i _ -> trs#remove_rule i);
				end else begin
					solver#add_assertion
						(smt_exists (fun i -> EV(gt_r_v i)) current_usables);
					comment putdot;
					solver#check;
					comment (fun _ -> prerr_string " removes:");
					List.iter
					(fun i ->
						if solver#get_bool (EV(gt_r_v i)) then
						(
							trs#remove_rule i;
							comment(fun _ -> prerr_string " "; prerr_int i;);
						);
					) current_usables;
					comment(fun _ -> prerr_newline ());
				end;
				proof (fun _ -> prerr_proof ());
				cpf output_cpf;
				x#pop;
				true
			with Inconsistent -> x#pop; false
	end;;
