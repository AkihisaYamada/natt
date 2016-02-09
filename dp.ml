open Util
open Term
open Trs
open Params

let mark fname = escape '#' ^ fname

let mark2 fname = escape '#' ^ escape '#' ^ fname

let rename_root renamer (Node(fty,fname,ss)) = Node(fty, renamer fname, ss)

let mark_KT98 =
	let rec sub fname (Node(fty,gname,ss) as s) =
		if fname = gname then
			Node(fty, mark fname, List.map (sub fname) ss) else s
	in
	fun (Node(fty,fname,ss) as s) ->
		match fty with
		| Fun -> rename_root mark s
		| Th "AC" -> Node(fty, mark fname, List.map (sub fname) ss)
		| _ -> raise (No_support "theory")

let mark_guard (Node(fty,fname,ss) as s) =
	match fty with
	| Fun -> rename_root mark s
	| Th _ -> Node(Fun, mark fname, [s])
	| _ -> raise (No_support "theory")

let mark_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun x -> x
	| AC_mark -> if params.acdp_mode = ACDP_KT98 then mark_KT98 else rename_root mark
	| AC_guard -> mark_guard

let mark_term (Node(fty,fname,ss) as s) =
	if fty = Fun then rename_root mark s else mark_ac s


let make_dp_table (trs:Trs.t) minimal =
	(* Relative: Moving duplicating or non-dominant weak rules to strict rules *)
	while
		trs#fold_eqs (fun i (l,r) ret ->
			if duplicating l r || not(trs#const_term r) then (
				trs#remove_eq i;
				trs#add_rule_extra l r MediumRule;
				true)
			else ret
		) false do () done;
	(* minimality can be assumed if all weak rules are size preserving *)
	minimal := trs#for_all_eq (fun i (l,r) -> size l >= size r);

	(* Main process *)
	let dp_table = Hashtbl.create 256 in
	let cnt = ref 0 in
	let add_dp l r strength =
		cnt := !cnt + 1;
		Hashtbl.add dp_table (!cnt) (l,r,strength);
	in
	
	(* Adding marked symbols *)
	let add_marked_symbol_default fname finfo =
		let minfo = trs#get_sym (mark fname) in
		minfo.symtype <- finfo.symtype;
		minfo.arity <- finfo.arity;
	in
	let add_marked_symbol_ac =
		match params.ac_mark_mode with
		| AC_unmark -> fun _ _ -> ()
		| AC_mark -> add_marked_symbol_default
		| AC_guard -> fun fname _ ->
			let minfo = trs#get_sym (mark fname) in
			minfo.symtype <- Fun;
			minfo.arity <- Arity 1;
	in
	let add_marked_symbol fname finfo =
		if trs#defines fname then begin
			if finfo.symtype = Fun then begin
				add_marked_symbol_default fname finfo;
			end else begin
				add_marked_symbol_ac fname finfo;
				if params.acdp_mode = ACDP_new then begin
					(* extensions have a different mark *)
					let minfo = trs#get_sym (mark2 fname) in
					minfo.symtype <- finfo.symtype;
					minfo.arity <- finfo.arity;
				end;
			end;
		end;
	in
	Hashtbl.iter add_marked_symbol trs#get_table;

	(* Generating dependency pairs *)
	let rec generate_dp_sub s strength (Node(gty,gname,ts) as t) =
		if trs#defines gname && not (is_subterm t s) then begin
			add_dp s (mark_term t) strength;
		end;
		List.iter (generate_dp_sub s strength) ts;
	in
	let generate_dp_default _ (Node(fty,fname,_) as l, r, strength) =
		generate_dp_sub (mark_term l) strength r
	in
	let ext_ac fty fname t = Node(fty, fname, [t; var "_1"]) in
	let generate_dp =
		match params.acdp_mode with
		| ACDP_new ->
			fun i (Node(fty,fname,_) as l, r, strength) ->
				if fty = Th "AC" then begin
					let xl = ext_ac fty fname l in
					let xr = ext_ac fty fname r in
					add_dp (rename_root mark2 xl) (rename_root mark2 xr) strength;
				end;
				generate_dp_default i (l,r,strength);
		| ACDP_KT98 ->
			fun i (Node(fty,fname,_) as l, r, strength) ->
				if fty = Th "AC" then begin
					let xl = ext_ac fty fname l in
					let xr = ext_ac fty fname r in
					add_dp (mark_term xl) (mark_term xr) strength;
				end;
				generate_dp_default i (l,r,strength);
		| _ ->
			fun i (Node(fty,fname,_) as l, r, strength) ->
				if fty = Th "AC" then begin
					let xl = ext_ac fty fname l in
					let xr = ext_ac fty fname r in
					generate_dp_default i (xl, xr, strength);
					minimal := false; (* Minimality cannot be assumed *)
				end;
	in
	trs#iter_rules_extra generate_dp;

	(* Additional rules for AC *)
	if params.ac_mark_mode = AC_mark then begin
		let ac_mark_handle fname finfo =
			if finfo.symtype = Th "AC" && trs#defines fname then begin
				let u s t = Node(finfo.symtype, fname, [s;t]) in
				let m s t = Node(Fun, mark fname, [s;t]) in
				let x = var "_1" in
				let y = var "_2" in
				let z = var "_3" in
				match params.acdp_mode with
				| ACDP_KT98 ->
					trs#add_eq (m (m x y) z) (m (u x y) z); (* AC-marked condition *)
					trs#add_eq (m (u x y) z) (m (m x y) z);
					trs#add_eq (u (u x y) z) (u x y); (* AC-deletion property *)
				| ACDP_GK01 ->
					trs#add_eq (m (u x y) z) (m x (u y z));
					trs#add_eq (m x (u y z)) (m (u x y) z);
				| ACDP_new ->
					add_dp (m (u x y) z) (m x (u y z)) WeakRule;
					add_dp (m x (u y z)) (m (u x y) z) WeakRule;
					add_dp (m (u x y) z) (m y z) WeakRule;
					add_dp (m x (u y z)) (m x y) WeakRule;
					let n s t = Node(Fun, mark2 fname, [s;t]) in
					add_dp (n (u x y) z) (n x (u y z)) WeakRule;
					add_dp (n x (u y z)) (n (u x y) z) WeakRule;
					add_dp (n (u x y) z) (n y z) WeakRule;
					add_dp (n x (u y z)) (n x y) WeakRule;
			end;
		in
		Hashtbl.iter ac_mark_handle trs#get_table;
	end;

	(* Return *)
	dp_table

let edged trs (_,r,_) (l,_,_) = trs#estimate_edge r l

module DG = Graph.Imperative.Digraph.Concrete(Int)
module Components = Graph.Components.Make(DG)
module SubDG =
	struct
		type t = DG.t * IntSet.t
		module V = Int
		let iter_vertex f (g,vs) = IntSet.iter f vs
		let iter_succ f (g,vs) = DG.iter_succ (fun v2 -> if IntSet.mem v2 vs then f v2) g
		let fold_succ f (g,vs) v a =
			DG.fold_succ (fun v2 b -> if IntSet.mem v2 vs then f v2 b else b) g v a
	end
module SubComponents = Graph.Components.Make(SubDG)

let make_dg trs dp_table =
	let dg = DG.create () in
	Hashtbl.iter (fun i _ -> DG.add_vertex dg i) dp_table;
	Hashtbl.iter
	(fun i1 dp1 ->
		Hashtbl.iter
		(fun i2 dp2 -> if edged trs dp1 dp2 then DG.add_edge dg i1 i2)
		dp_table
	)
	dp_table;
	dg

let notsingle dg =
	function
	| [v] -> DG.mem_edge dg v v
	| _ -> true

let get_sccs dg =
	List.filter (notsingle dg) (Components.scc_list dg)

let get_subsccs dg dpset =
	List.filter (notsingle dg) (SubComponents.scc_list (dg,dpset))

class dg trs =
	let min = ref true in
	let init_dp_table = make_dp_table trs min in
	let init_dg = make_dg trs init_dp_table in
	(* list of lists to list of sets *)
	let ll2ls = List.map (List.fold_left (fun s e -> IntSet.add e s) IntSet.empty) in
	object (x)
		val dp_table = init_dp_table
		val dg = init_dg
		method minimal = !min
		method remove_dp i = DG.remove_vertex dg i; Hashtbl.remove dp_table i;
		method replace_dp i l r = Hashtbl.replace dp_table i (l,r,StrictRule);
		method get_subdg (scc:IntSet.t) = (dg,scc)
		method get_sccs = ll2ls (get_sccs dg)
		method get_subsccs dpset = ll2ls (get_subsccs dg dpset)
		method get_size = Hashtbl.length dp_table
		method find_dp i = let (l,r,_) = Hashtbl.find dp_table i in (l,r)
		method get_dp_size i = let (l,r) = x#find_dp i in size l + size r
		method iter_dps f = Hashtbl.iter (fun i (l,r,_) -> f i (l,r)) dp_table
		method get_dps = Hashtbl.fold (fun i (l,r,_) ps -> (i,(l,r))::ps) dp_table []
		method output_dps os = output_tbl os output_rule "   #" dp_table
		method is_strict i = let (_,_,s) = Hashtbl.find dp_table i in s = StrictRule
		method is_weak i = let (_,_,s) = Hashtbl.find dp_table i in s = WeakRule
	end;;
