open Util
open Term
open Trs
open Params

let mark_name fname = "#"^fname
let mark (Node(fty,fname,ss) as s) =
	if fty = Th "AC" then
		match params.ac_mark_mode with
		| AC_unmark -> s
		| AC_mark -> Node(fty, mark_name fname, ss)
		| AC_guard -> Node(Fun, mark_name fname, [s])
	else
		Node(fty, mark_name fname, ss)

let make_dp_table (trs:Trs.t) =
	trs#iter_eqs (fun i (l,r) ->
		if duplicating l r || not(trs#const_term r) then begin
			trs#remove_eq i;
			trs#add_rule l r;
		end;
	);
	let dp_table = Hashtbl.create 256 in
	let cnt = ref 0 in
	let add_dp l r =
		cnt := !cnt + 1;
		Hashtbl.add dp_table (!cnt) (l,r);
	in
	let add_marked_symbol fname finfo =
		if trs#defines fname then begin
			if finfo.symtype = Th "AC" then
				match params.ac_mark_mode with
				| AC_unmark -> ()
				| AC_mark ->
					let mname = mark_name fname in
					let minfo = trs#get_sym mname in
					minfo.symtype <- finfo.symtype;
					minfo.arity <- finfo.arity;
					begin
						let u s t = Node(Th "AC", fname, [s;t]) in
						let m s t = Node(Th "AC", mname, [s;t]) in
						let x = var "_1" in
						let y = var "_2" in
						let z = var "_3" in
						match params.acdp_mode with
						| ACDP_GK01 -> trs#add_eq (m (u x y) z) (m x (u y z));
						| _ -> trs#add_eq (m (m x y) z) (m (u x y) z);
					end;
				| AC_guard ->
					let minfo = trs#get_sym (mark_name fname) in
					minfo.symtype <- Fun;
					minfo.arity <- Arity 1;
			else
			let minfo = trs#get_sym (mark_name fname) in
			minfo.symtype <- finfo.symtype;
			minfo.arity <- finfo.arity;
		end;
	in
	Hashtbl.iter add_marked_symbol trs#get_table;
	let rec sub s (Node(gty,gname,ts) as t) =
		if trs#defines gname && not (is_subterm t s) then
			add_dp s (mark t);
		List.iter (sub s) ts;
	in
	let ext_ac fty fname t = Node(fty,fname,[t; var "_1"]) in
	let iterer _ (Node(fty,fname,_) as l, r) =
		if fty = Th "AC" && params.acdp_mode <> ACDP_new then begin
			let xl = ext_ac fty fname l in
			let xr = ext_ac fty fname r in
			if params.acdp_mode = ACDP_KT98 then begin
				add_dp (mark xl) (mark xr);
			end else begin
				sub (mark xl) xr;
			end;
		end;
		sub (mark l) r;
	in
	trs#iter_rules iterer;
	dp_table

let edged trs (_,r) (l,_) = trs#estimate_edge r l

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
	let init_dp_table = make_dp_table trs in
	let init_dg = make_dg trs init_dp_table in
	(* list of lists to list of sets *)
	let ll2ls = List.map (List.fold_left (fun s e -> IntSet.add e s) IntSet.empty) in
	object (x)
		val dp_table = init_dp_table
		val dg = init_dg
		method remove_dp i = DG.remove_vertex dg i; Hashtbl.remove dp_table i;
		method replace_dp i l r = Hashtbl.replace dp_table i (l,r);
		method get_subdg (scc:IntSet.t) = (dg,scc)
		method get_sccs = ll2ls (get_sccs dg)
		method get_subsccs dpset = ll2ls (get_subsccs dg dpset)
		method get_size = Hashtbl.length dp_table
		method find_dp i = Hashtbl.find dp_table i
		method get_dp_size i = let (l,r) = x#find_dp i in size l + size r
		method iter_dps f = Hashtbl.iter f dp_table
		method get_dps = Hashtbl.fold (fun i ri ps -> (i,ri)::ps) dp_table []
		method output_dps os = output_tbl os output_rule "   #" dp_table
	end;;
