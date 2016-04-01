open Util
open Sym
open Term
open Trs
open Params
open Io

let mark_root (Node((f:#sym),ss)) = Node(mark_sym f, ss)

let mark_term_KT98 =
	let rec sub (f:#sym) (Node(g,ss) as s) =
		if f#equals g then
			Node(mark_sym f, List.map (sub f) ss) else s
	in
	fun (Node(f,ss) as s) ->
		if f#is_associative then
			Node(mark_sym f, List.map (sub f) ss)
		else mark_root s

let guard_term (Node(f,ss) as s) = Node(new sym_marked Fun f#name, [s])

let mark_term_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun x -> x
	| AC_mark ->
		if params.acdp_mode = ACDP_KT98 then mark_term_KT98 else mark_root
	| AC_guard -> guard_term

let mark_term (Node(f,ss) as s) =
	if f#is_theoried then mark_term_ac s else mark_root s

(* Adding marked symbols *)

let add_marked_symbol_default (trs : #trs) f =
	let f' = trs#get_sym (mark_sym f) in
	f'#set_arity f#arity;;

let add_marked_symbol_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun _ _ -> ()
	| AC_mark -> add_marked_symbol_default
	| AC_guard -> fun trs f ->
		let f' = trs#get_sym (new sym_marked f#ty f#name) in
		f'#set_arity 1;;

let add_marked_symbols (trs : #trs) =
	let iterer f =
		if f#is_defined then begin
			if f#ty = Fun then begin
				add_marked_symbol_default trs f;
			end else begin
				add_marked_symbol_ac trs f;
			end;
		end;
	in
	trs#iter_syms iterer;;



(* For the new AC-DP *)
let add_marked_symbols_ac trs =
	let iterer f =
		if f#ty <> Fun && f#is_defined then begin
			add_marked_symbol_ac trs f;
		end;
	in
	trs#iter_syms iterer;;




module DG = Graph.Imperative.Digraph.Concrete(Int)
module Components = Graph.Components.Make(DG)
module Topological = Graph.Topological.Make(DG)

module SubDG = struct
	type t = DG.t * IntSet.t
	module V = Int
	let iter_vertex f (g,vs) = IntSet.iter f vs
	let iter_succ f (g,vs) = DG.iter_succ (fun v2 -> if IntSet.mem v2 vs then f v2) g
	let fold_succ f (g,vs) v a =
		DG.fold_succ (fun v2 b -> if IntSet.mem v2 vs then f v2 b else b) g v a
end

module SubComponents = Graph.Components.Make(SubDG)


class dg (trs : trs) (estimator : Estimator.t) =
	(* list of lists to list of sets *)
	let ll2ls = List.map (List.fold_left (fun s e -> IntSet.add e s) IntSet.empty) in
	object (x)
		val mutable minimal = true
		val dp_table = Hashtbl.create 256
		val dg = DG.create ()
		val mutable dp_cnt = 0
		val mutable need_extended_rules =
			trs#is_theoried && params.acdp_mode = ACDP_new

		method add_dp lr =
			dp_cnt <- dp_cnt + 1;
			Hashtbl.add dp_table dp_cnt lr;

		(* Generate dependency pairs *)
		method generate_dp =
			let rec generate_dp_sub strength s (Node(g,ts) as t) =
				if trs#defines g && not (strict_subterm t s) then begin
					x#add_dp (new rule strength s (mark_term t));
				end;
				List.iter (generate_dp_sub strength s) ts;
			in
			let generate_dp_default rule =
				generate_dp_sub rule#strength (mark_term rule#l) rule#r
			in
			match params.acdp_mode with
			| ACDP_new -> generate_dp_default
			| ACDP_union -> fun rule ->
				generate_dp_default rule;
				if (root rule#l)#is_theoried then begin
					let iterer xrule = x#add_dp (map_rule mark_term xrule) in
					List.iter iterer (extended_rules rule);
				end;
			| ACDP_KT98 -> fun rule ->
				generate_dp_default rule;
				if (root rule#l)#is_theoried then begin
					let iterer xrule = x#add_dp (map_rule mark_term xrule) in
					List.iter iterer (extended_rules rule);
				end;
			| ACDP_ALM10 | ACDP_GK01 -> fun rule ->
				generate_dp_default rule;
				if (root rule#l)#is_theoried then begin
					List.iter generate_dp_default (extended_rules rule);
				end;

		method init =
			(* Relative: Moving duplicating or non-dominant weak rules to *medium* rules *)
			while trs#fold_rules (fun i rule ret ->
					if rule#is_weak &&
						(rule#is_duplicating || not(trs#relative_const rule#r)) then (
						trs#replace_rule i (medium_rule rule#l rule#r);
						true)
					else ret
				) false
			do () done;
			(* minimality can be assumed if all weak rules are size preserving *)
			let tester i rule =
				rule#is_weak && rule#is_size_increasing && (
					log (puts "Detected size-increasing weak rule " << put_int i <<
						puts ". Disabling minimality." << endl
					); true)
			in
			if trs#exists_rule tester then begin
				minimal <- false;
			end;
			if trs#is_theoried &&
				(params.acdp_mode = ACDP_new || params.acdp_mode = ACDP_union)
			then begin
				(* turn AC theory into weak rules *)
				trs#th_to_rules;
			end;
			(* Main process *)
			add_marked_symbols trs;
			let iterer i rule = x#generate_dp rule in
			trs#iter_rules iterer;
		
			(* Additional rules for AC *)
			let add_eq s t =
				trs#add_rule (weak_rule s t);
				problem trs#output_last_rule;
			in
			let v1 = var "_1" in
			let y = var "_2" in
			let z = var "_3" in
			let ac_mark_handle (f:#sym_detailed) =
				if f#is_associative && f#is_defined then begin
					let u s t = app f [s;t] in
					let m =
						if params.ac_mark_mode = AC_mark then
							fun s t -> mark_root (u s t)
						else u
					in
					match params.acdp_mode with
					| ACDP_KT98 ->
						(* AC-deletion property *)
						add_eq (u (u v1 y) z) (u v1 y);
						if not f#is_commutative then begin
							add_eq (u v1 (u y z)) (u y z);
						end;
						(* AC-marked condition *)
						add_eq (m (m v1 y) z) (m (u v1 y) z);
						add_eq (m (u v1 y) z) (m (m v1 y) z);
						(* AC-deletion property is needed also for marked ones! *)
						add_eq (m (m v1 y) z) (m v1 y);
						if not f#is_commutative then begin
							add_eq (m v1 (m y z)) (m v1 (u y z));
							add_eq (m v1 (u y z)) (m v1 (m y z));
							add_eq (m v1 (m y z)) (m y z);
						end;
					| ACDP_GK01 ->
						if params.ac_mark_mode = AC_mark then begin
							add_eq (m (u v1 y) z) (m v1 (u y z));
							if not f#is_commutative then begin
								add_eq (m v1 (u y z)) (m (u v1 y) z);
							end;
						end;
					| ACDP_ALM10 ->
						if params.ac_mark_mode = AC_mark then begin
							add_eq (m (u v1 y) z) (m v1 (u y z));
							if not f#is_commutative then begin
								add_eq (m v1 (u y z)) (m (u v1 y) z);
							end;
						end;
						add_eq (m (u v1 y) z) (m v1 y);
						if not f#is_commutative then begin
							add_eq (m v1 (u y z)) (m y z);
						end;
					| _ -> ()
				end;
			in
			trs#iter_syms ac_mark_handle;
			x#make_dg;

(* Estimated dependency graph *)

		method private make_dg =
			log estimator#output;
			let edged_KT98 src tgt =
				if (root src#l)#is_associative then
					List.exists (fun r' -> estimator#connects r' tgt#l) (top_ac_subterms src#r)
				else estimator#connects src#r tgt#l
			in
			let edged =
				if params.acdp_mode = ACDP_KT98 then edged_KT98
				else fun src tgt ->
					let Node(f,ss) = src#r in
					let Node(g,ts) = tgt#l in
					f#equals g &&
					if f#is_commutative then
						(* commutativity is taken specially *)
						match ss, ts with
						| [s1;s2], [t1;t2] ->
							(estimator#narrows s1 t1 && estimator#narrows s2 t2) ||
							(estimator#narrows s1 t2 && estimator#narrows s2 t1)
						| _ -> raise (No_support "nonbinary commutative symbol")
					else List.for_all2 estimator#narrows ss ts
			in
			Hashtbl.iter (fun i _ -> DG.add_vertex dg i) dp_table;
			Hashtbl.iter
			(fun i1 dp1 ->
				Hashtbl.iter
				(fun i2 dp2 -> if edged dp1 dp2 then DG.add_edge dg i1 i2)
				dp_table
			)
			dp_table;

		method private make_ac_ext =
			x#iter_dps (fun i _ -> x#remove_dp i);
			let iterer i rule =
				if (root rule#l)#is_theoried then begin
					if rule#is_strict then begin
						let iterer xrule = x#add_dp (map_rule mark_term xrule) in
						List.iter iterer (extended_rules rule);
					end else begin
						x#generate_dp rule;
					end;
				end;
			in
			trs#iter_rules iterer;
			x#make_dg;

		method next = (* if there is a next problem, then init it and say true *)
			need_extended_rules && (
				x#make_ac_ext;
				need_extended_rules <- false;
				true
			)
		method minimal = minimal
		method get_subdg scc = (dg, IntSet.of_list scc)
		(* reverse SCCs, for CeTA *)
		method get_sccs = List.rev (Components.scc_list dg)
		method get_subsccs dps = List.rev (SubComponents.scc_list (dg, IntSet.of_list dps))
		method triv_scc = function
			| [v] -> not (DG.mem_edge dg v v)
			| _ -> false
		method get_size = Hashtbl.length dp_table
		method find_dp = Hashtbl.find dp_table
		method get_dp_size i = let dp = x#find_dp i in dp#size
		method iter_dps f = Hashtbl.iter f dp_table
		method get_dps = Hashtbl.fold (fun i dp dps -> (i,dp)::dps) dp_table []
		method remove_dp i = DG.remove_vertex dg i; Hashtbl.remove dp_table i;
		method replace_dp i dp = Hashtbl.replace dp_table i dp;
		method modify_dp i l r = x#replace_dp i (new rule (x#find_dp i)#strength l r)
		method output_dp : 'a. int -> (#Io.printer as 'a) -> unit = fun i pr ->
			output_tbl_index pr "   #" (i, x#find_dp i)
		method output_dp_xml : 'a. int -> (#Io.printer as 'a) -> unit = fun i ->
			(x#find_dp i)#output_xml
		method output_dps : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			output_tbl pr "   #" dp_table
		method output_dps_xml : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			x#iter_dps (fun _ rule -> rule#output_xml pr)
		method output_scc_xml : 'a. int list -> (#Io.printer as 'a) -> unit = fun scc pr ->
			List.iter (fun i -> x#output_dp_xml i pr) scc
		method iter_edges f = DG.iter_edges f dg
		method output_edges : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "Edges:";
			pr#enter 2;
			let iterer i _ =
				let succ = DG.succ dg i in
				if succ <> [] then begin
					pr#endl;
					pr#putc '#';
					pr#put_int i;
					pr#puts " -->";
					Abbrev.put_ints " #" succ pr;
				end;
			in
			x#iter_dps iterer;
			pr#leave 2;
			pr#endl;
	end;;
