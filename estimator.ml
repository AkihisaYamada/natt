open Util
open Sym
open Term
open Trs
open Params

type 'a connects_formula =
	| False
	| Connects of ('a * 'a) list

let connects_and a b =
	match a, b with
	| False, _ -> a
	| _, False -> b
	| Connects aa, Connects bb -> Connects (aa@bb)

(* symbol transition graph *)
module SymG = Graph.Imperative.Digraph.Concrete(StrHashed)
module SymGoper = Graph.Oper.I(SymG)

class virtual t (trs:#trs) = object (x)

	method virtual may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool

	method unifies : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
	fun (Node(f,ss)) (Node(g,ts)) ->
		f#is_var ||
		g#is_var ||
		f#equals g &&
		match f#ty with
		| Fun -> List.for_all2 x#unifies ss ts
		| Th "C" ->
			(	match ss, ts with
				| [s1;s2], [t1;t2] ->
					(x#unifies s1 t1 && x#unifies s2 t2) ||
					(x#unifies s1 t2 && x#unifies s2 t1)
				| _ -> raise (No_support "nonbinary commutative symbol")
			)
		| _ -> true

	method may_connect_n : 'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun n (Node(f,ss)) (Node(g,ts)) ->
			f#equals g &&
			match f#ty with
			| Fun -> List.for_all2 (x#may_reach_n n) ss ts
			| Th "C" ->
				(	match ss, ts with
					| [s1;s2], [t1;t2] ->
						(x#may_reach_n n s1 t1 && x#may_reach_n n s2 t2) ||
						(x#may_reach_n n s1 t2 && x#may_reach_n n s2 t1)
					| _ -> raise (No_support "nonbinary commutative symbol")
				)
			| _ -> true

	method may_reach_n : 'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun n (Node(f,ss) as s) t ->
			f#is_var ||
			(root t)#is_var ||
			if n = 0 then x#may_reach_0 s t
			else
				x#may_connect_n (n-1) s t ||
				let tester i =
					let rule = trs#find_rule i in
					let Node(_,ls) = rule#l in
					List.for_all2 (x#may_reach_n n) ss ls &&
					x#may_reach_n (n-1) rule#r t
				in
				let f = trs#find_sym f in
				Rules.exists tester f#weakly_defined_by ||
				Rules.exists tester f#defined_by

	method may_connect : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun s t -> x#may_connect_n params.edge_length s t

	method may_reach : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun s t -> x#may_reach_n params.edge_length s t

	method find_matchable :
	'a. (#sym as 'a) term -> Rules.elt list = fun s ->
		let f = trs#find_sym (root s) in
		let folder i ret =
			if x#may_connect_n 0 s (trs#find_rule i)#l then i::ret else ret
		in
		Rules.fold folder f#weakly_defined_by
		(Rules.fold folder f#defined_by [])

	method estimate_paths :
	'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> (int * int list) list =
	fun lim (Node(f,_) as s) (Node(g,_) as t) ->
		if term_eq s t || f#is_var || g#is_var then
			[(0,[])]
		else if lim > 0 then
			let init = if x#unifies s t then [(1,[])] else [] in
			let folder ret i =
				List.map (path_append (1,[i]))
					(x#estimate_paths (lim-1) (trs#find_rule i)#r t) @ ret
			in
			List.fold_left folder init (x#find_matchable s)
		else
			[]
	
	method instantiate_edge :
	int ref -> int -> sym term -> sym term -> (int * sym Subst.t) list =
	fun cnt ->
		let rec sub1 lim s t =
			let paths = x#estimate_paths (min 4 lim) s t in
			let folder ret (c,is) =
				let cus = instantiate_path (lim-c) s is t in
				List.iter (dbg s is t) cus; cus @ ret
			in
			List.fold_left folder [] paths
		and sub2 lim ss ts =
			match ss, ts with
			| [], [] -> [(0, new Subst.t)]
			| (s::ss), (t::ts) ->
				let mapper (c1,u1) =
					let ss' = List.map u1#subst ss in
					let ts' = List.map u1#subst ts in
					List.map (cu_append (c1,u1)) (sub2 (lim-c1) ss' ts')
				in
				List.concat (List.map mapper (sub1 lim s t))
			| _ -> []
		and instantiate_path lim (Node(f,ss) as s) is (Node(g,ts) as t) =
			match is with
			| [] ->
				if term_eq s t then [(0,new Subst.t)]
				else if f#is_var then
					if StrSet.mem f#name (varset t) then [] else [(0,Subst.singleton f t)]
				else if g#is_var then
					if StrSet.mem g#name (varset s) then [] else [(0,Subst.singleton g s)]
				else
					(if f#equals g then
						sub2 lim ss ts
					else  []
					) @ sub1 (lim-1) s t
			| i::is ->
				cnt := !cnt + 1;
				let v = "i" ^ string_of_int !cnt in
				let rule = trs#find_rule i in
				let l = Subst.vrename v rule#l in
				let r = Subst.vrename v rule#r in
				let rec sub3 cus =
					match cus with
					| [] -> []
					| (c1,u1)::cus ->
						let r' = u1#subst r in
						let t' = u1#subst t in
						List.map (cu_append (c1+1,u1)) (instantiate_path (lim - c1) r' is t') @
						sub3 cus
				in
				let ret = sub3 (sub1 lim s l) in
				ret
		in
		fun lim (Node(f,ss)) (Node(g,ts)) ->
			if f#equals g then sub2 lim ss ts else []

	method output : 'a. (#Io.printer as 'a) -> unit = fun os -> ()
end;;

let tcap (trs:#trs) : t = object (x)
	inherit t trs
	method may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
	fun s t -> true
end;;

let sym_trans (trs:#trs) : t =
	let collapsable = ref [] in
	let sym_g = SymG.create () in
	let () =
		SymG.add_vertex sym_g  ""; (* this vertex represents arbitrary symbol *)
		let add_sym f =
			if f#is_fun then begin
				SymG.add_vertex sym_g f#name;
				SymG.add_edge sym_g "" f#name;
			end;
		in
		trs#iter_syms add_sym;
		let add_edge _ rule =
			let f = root rule#l in
			let g = root rule#r in
			if g#is_var then begin
				collapsable := f :: !collapsable;
				SymG.add_edge sym_g f#name "";
			end else begin
				SymG.add_edge sym_g f#name g#name;
			end;
		in
		trs#iter_rules add_edge;
		ignore (SymGoper.add_transitive_closure sym_g);
		SymG.remove_vertex sym_g ""; (* Remove the temporal vertex *)
	in
	let trans_sym : #sym -> #sym -> bool = fun f g ->
		f#equals g || SymG.mem_edge sym_g f#name g#name
	in
	object (x)
		inherit t trs
		method may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
			fun (Node(f,ss) as s) (Node(g,ts) as t) -> trans_sym f g
		method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "Symbol transition graph:";
			pr#enter 4;
			let iterer (f:#sym_detailed) =
				if f#is_defined then begin
					let succ = SymG.succ sym_g f#name in
					pr#endl;
					f#output pr;
					pr#puts "\t-->";
					List.iter (fun gname -> pr#putc ' '; pr#puts gname;) succ;
				end;
			in
			trs#iter_syms iterer;
			pr#leave 2;
			pr#endl;
			pr#puts "Collapsable symbols: {";
			List.iter (fun (f : #sym) -> pr#putc ' '; f#output pr;) !collapsable;
			pr#puts " }";
			pr#leave 2;
			pr#endl;
	end;;

