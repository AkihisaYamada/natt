open Util
open Term
open Trs
open Params

let mark_name name = escape '#' ^ name
let unmark_name name = String.sub name 2 (String.length name - 2)

let string_prefix s t =
	let n = String.length t in
	String.length s >= n &&
	let rec sub i =
		i > n || s.[i] = t.[i] && sub (i+1)
	in
	sub 0

let marked_name name = string_prefix name (escape '#')

let mark_sym f =
	let fty =
		match f#ty with
		| Th "AC" -> Th "C"
		| fty -> fty
	in
	new sym_basic fty (mark_name f#name)

let mark_sym_KT98 f = new sym_basic f#ty (escape '#' ^ f#name)

let mark_root (Node(f,ss)) = Node(mark_sym f, ss)

let mark_term_KT98 =
	let rec sub (f:#sym) (Node(g,ss) as s) =
		if f#equals g then
			Node(mark_sym_KT98 f, List.map (sub f) ss) else s
	in
	fun (Node(f,ss) as s) ->
		match f#ty with
		| Th "AC" -> Node(mark_sym_KT98 f, List.map (sub f) ss)
		| _ -> mark_root s

let guard_term (Node(f,ss) as s) =
	Node(new sym_basic Fun (mark_name f#name), [s])

let mark_term_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun x -> x
	| AC_mark ->
		if params.acdp_mode = ACDP_KT98 then mark_term_KT98 else mark_root
	| AC_guard -> guard_term

let mark_term (Node(f,ss) as s) =
	if f#is_theoried then mark_term_ac s else mark_root s


let ext_ac f t = Node(f, [t; var "_1"])

(* Adding marked symbols *)

let add_marked_symbol_default (trs:trs) f =
	let f' = trs#get_sym (mark_sym f) in
	f'#set_arity f#arity;;

let add_marked_symbol_ac : trs -> #sym_detailed -> unit =
	match params.ac_mark_mode with
	| AC_unmark -> fun _ _ -> ()
	| AC_mark -> fun trs f ->
		let f' = trs#get_sym (mark_sym f) in
		f'#set_arity f#arity;
	| AC_guard -> fun trs f ->
		let f' = trs#get_sym_name (mark_name f#name) in
		f'#set_arity 1;;

let add_marked_symbols (trs:trs) =
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

let make_dp_table (trs:trs) minimal dp_table =
	(* Relative: Moving duplicating or non-dominant weak rules to *medium* rules *)
	while
		trs#fold_rules (fun i rule ret ->
			if rule#is_weak && (rule#is_duplicating || not(trs#relative_const rule#r)) then (
				trs#replace_rule i (medium_rule rule#l rule#r);
				true)
			else ret
		) false do () done;
	(* minimality can be assumed if all weak rules are size preserving *)
	let tester i rule =
		rule#is_weak && rule#is_size_increasing && (
			log (fun _ ->
				prerr_string "Detected size-increasing weak rule ";
				prerr_int i;
				prerr_endline ". Disabling minimality.";
			); true)
	in
	if trs#exists_rule tester then begin
		minimal := false;
	end;

	(* Main process *)
	let cnt = ref 0 in
	let add_dp lr =
		cnt := !cnt + 1;
		Hashtbl.add dp_table (!cnt) lr;
	in
	
	add_marked_symbols trs;

	(* Generating dependency pairs *)
	let rec generate_dp_sub strength s (Node(g,ts) as t) =
		if trs#strictly_defines g && not (strict_subterm t s) then begin
			add_dp (new rule strength s (mark_term t));
		end;
		List.iter (generate_dp_sub strength s) ts;
	in
	let generate_dp_default i rule =
		generate_dp_sub rule#strength (mark_term rule#l) rule#r
	in
	let generate_dp =
		match params.acdp_mode with
		| ACDP_new -> generate_dp_default
		| ACDP_KT98 ->
			fun i rule ->
				let f = root rule#l in
				generate_dp_default i rule;
				if f#ty = Th "AC" then begin
					let xl = ext_ac f rule#l in
					let xr = ext_ac f rule#r in
					add_dp (new rule rule#strength (mark_term xl) (mark_term xr));
				end;
		| _ ->
			fun i rule ->
				let f = root rule#l in
				generate_dp_default i rule;
				if f#ty = Th "AC" then begin
					let xl = ext_ac f rule#l in
					let xr = ext_ac f rule#r in
					generate_dp_default i (new rule rule#strength xl xr);
				end;
	in
	trs#iter_rules (fun i rule -> if not rule#is_weak then generate_dp i rule;);

	(* Additional rules for AC *)
	let add_eq s t =
		trs#add_rule (weak_rule s t);
		problem trs#output_last_rule;
	in
	let ac_mark_handle f =
		if f#ty = Th "AC" && f#is_defined then begin
			let u s t = app f [s;t] in
			let m =
				if params.ac_mark_mode = AC_mark then
					fun s t -> mark_root (u s t)
				else u
			in
			let x = var "_1" in
			let y = var "_2" in
			let z = var "_3" in
			match params.acdp_mode with
			| ACDP_KT98 ->
				add_eq (m (m x y) z) (m (u x y) z); (* AC-marked condition *)
				add_eq (m (u x y) z) (m (m x y) z);
				add_eq (u (u x y) z) (u x y); (* AC-deletion property *)
				if params.ac_mark_mode = AC_mark then begin
					(* AC-deletion property is needed also for marked ones! *)
					add_eq (m (m x y) z) (m x y);
				end;
			| ACDP_GK01 ->
				if params.ac_mark_mode = AC_mark then begin
					add_eq (m (u x y) z) (m x (u y z));
(*					add_eq (m x (u y z)) (m (u x y) z);
*)				end;
				minimal := false; (* Minimality cannot be assumed *)
			| ACDP_ALM10 ->
				if params.ac_mark_mode = AC_mark then begin
					add_eq (m (u x y) z) (m x (u y z));
(*					add_eq (m x (u y z)) (m (u x y) z);
*)				end;
				add_eq (m (u x y) z) (m x y);
			| ACDP_new ->
				if params.ac_mark_mode = AC_mark then begin
					add_dp (weak_rule (m (u x y) z) (m x (u y z)));
(*					add_dp (weak_rule (m x (u y z)) (m (u x y) z));
*)				end;
				add_dp (weak_rule (m (u x y) z) (m y z));
(*				add_dp (weak_rule (m x (u y z)) (m x y));
*)		end;
	in
	trs#iter_syms ac_mark_handle;;


(* For the new AC-DP *)
let add_marked_symbols_ac trs =
	let iterer f =
		if f#ty <> Fun && f#is_defined then begin
			add_marked_symbol_ac trs f;
		end;
	in
	trs#iter_syms iterer;;

let make_ac_ext (trs:trs) dp_table =
	let cnt = ref 0 in
	let add_dp rule =
		cnt := !cnt + 1;
		Hashtbl.add dp_table (!cnt) rule;
	in
	let generate_dp i rule =
		let f = root rule#l in
		if rule#is_strict && f#ty = Th "AC" then begin
			let xl = ext_ac f rule#l in
			let xr = ext_ac f rule#r in
			add_dp (new rule rule#strength (mark_term xl) (mark_term xr));
		end;
	in
	trs#iter_rules generate_dp;
	let ac_mark_handle f =
		if f#is_defined && f#ty = Th "AC" then begin
			let u s t = app f [s;t] in
			let m =
				if params.ac_mark_mode = AC_mark then fun s t -> mark_root (u s t)
				else u
			in
			let x = var "_1" in
			let y = var "_2" in
			let z = var "_3" in
			if params.ac_mark_mode = AC_mark then begin
				add_dp (weak_rule (m (u x y) z) (m x (u y z)));
(*				add_dp (weak_rule (m x (u y z)) (m (u x y) z));
*)			end;
			add_dp (weak_rule (m (u x y) z) (m y z));
(*			add_dp (weak_rule (m x (u y z)) (m x y));
*)		end;
	in
	trs#iter_syms ac_mark_handle;
	add_marked_symbols_ac trs;;



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


(* Estimated dependency graph *)

let make_dg (trs:trs) (estimator:Estimator.t) dp_table dg =
	log estimator#output_sym_graph;
	let edged_KT98 src tgt =
		if (root src#l)#ty = Th "AC" then
			List.exists (fun r' -> estimator#connects r' tgt#l) (top_ac_subterms src#r)
		else estimator#connects src#r tgt#l
	in
	let edged =
		if params.acdp_mode = ACDP_KT98 then edged_KT98
		else fun src tgt -> estimator#connects src#r tgt#l
	in
	Hashtbl.iter (fun i _ -> DG.add_vertex dg i) dp_table;
	Hashtbl.iter
	(fun i1 dp1 ->
		Hashtbl.iter
		(fun i2 dp2 -> if edged dp1 dp2 then DG.add_edge dg i1 i2)
		dp_table
	)
	dp_table;;

let notsingle dg =
	function
	| [v] -> DG.mem_edge dg v v
	| _ -> true

let get_sccs dg =
	List.filter (notsingle dg) (Components.scc_list dg)

let get_subsccs dg dpset =
	List.filter (notsingle dg) (SubComponents.scc_list (dg,dpset))

class dg (trs:trs) (estimator:Estimator.t) =
	(* list of lists to list of sets *)
	let ll2ls = List.map (List.fold_left (fun s e -> IntSet.add e s) IntSet.empty) in
	object (x)
		val min = ref true
		val dp_table = Hashtbl.create 256
		val dg = DG.create ()
		method init = make_dp_table trs min dp_table; make_dg trs estimator dp_table dg;
		method init_ac_ext = make_ac_ext trs dp_table; make_dg trs estimator dp_table dg;
		method minimal = !min
		method get_subdg (scc:IntSet.t) = (dg,scc)
		method get_sccs = ll2ls (get_sccs dg)
		method get_subsccs dpset = ll2ls (get_subsccs dg dpset)
		method get_size = Hashtbl.length dp_table
		method find_dp = Hashtbl.find dp_table
		method get_dp_size i = let dp = x#find_dp i in dp#size
		method iter_dps f = Hashtbl.iter f dp_table
		method get_dps = Hashtbl.fold (fun i dp dps -> (i,dp)::dps) dp_table []
		method remove_dp i = DG.remove_vertex dg i; Hashtbl.remove dp_table i;
		method replace_dp i dp = Hashtbl.replace dp_table i dp;
		method modify_dp i l r = x#replace_dp i (new rule (x#find_dp i)#strength l r)
		method output_dps os = output_tbl os "   #" dp_table
		method iter_edges f = DG.iter_edges f dg
		method output_edges os =
			output_string os "Edges:\n";
			let iterer i _ =
				let succ = DG.succ dg i in
				if succ <> [] then begin
					output_string os ("  #" ^ string_of_int i ^ " -->");
					Abbrev.output_ints os " #" succ;
					output_char os '\n';
				end;
			in
			x#iter_dps iterer;

	end;;
