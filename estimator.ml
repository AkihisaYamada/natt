open Util
open Term
open Trs
open Params

(* symbol transition graph *)
module SymG = Graph.Imperative.Digraph.Concrete(StrHashed)
module SymGoper = Graph.Oper.I(SymG)

class ['f] t (trs : 'f #trs) =

	let init_sym_g =
		let sym_g = SymG.create () in
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
			SymG.add_edge sym_g f#name (if g#is_var then "" else g#name);
		in
		trs#iter_rules add_edge;
		ignore (SymGoper.add_transitive_closure sym_g);
		sym_g
	in

	object (x)
		val sym_g = init_sym_g
		method trans_sym :
		'a 'b. (#sym as 'a) -> (#sym as 'b) -> bool = fun f g ->
			SymG.mem_edge sym_g f#name "" || SymG.mem_edge sym_g f#name g#name
(* estimations *)
		method narrows :
		'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun (Node(f,ss) as s) (Node(g,ts) as t) ->
			f#is_var ||
			g#is_var ||
			x#is_redex_candidate s && x#trans_sym f g ||
			x#connects s t
		method connects :
		'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun (Node(f,ss)) (Node(g,ts)) ->
			f#equals g &&
			(	match f#ty with
				| Fun -> List.for_all2 x#narrows ss ts
				| Th "C" ->
					(	match ss, ts with
						| [s1;s2], [t1;t2] ->
							(x#narrows s1 t1 && x#narrows s2 t2) ||
							(x#narrows s1 t2 && x#narrows s2 t1)
						| _ -> raise (No_support "nonbinary commutative symbol")
					)
				| _ -> true
			)
		method is_redex_candidate :
		'a. (#sym as 'a) term -> bool = fun (Node(f,ss)) ->
			let tester i =
				let Node(_,ls) = (trs#find_rule i)#l in
				List.for_all2 x#narrows ss ls
			in
			let f = trs#find_sym f in
			Rules.exists tester f#weakly_defined_by ||
			Rules.exists tester f#defined_by
		method find_matchable :
		'a. (#sym as 'a) term -> Rules.elt list = fun s ->
			let f = trs#find_sym (root s) in
			let folder i ret =
				if x#connects s (trs#find_rule i)#l then i::ret else ret
			in
			Rules.fold folder f#weakly_defined_by
			(Rules.fold folder f#defined_by [])

		method estimate_paths :
		'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> (int * int list) list =
		fun lim (Node(f,_) as s) (Node(g,_) as t) ->
			if term_eq s t || f#is_var || g#is_var then
				[(0,[])]
			else if lim > 0 then
				let init = if x#connects s t then [(1,[])] else [] in
				let folder ret i =
					List.map (path_append (1,[i]))
						(x#estimate_paths (lim-1) (trs#find_rule i)#r t) @ ret
				in
				List.fold_left folder init (x#find_matchable s)
			else
				[]
		
		method instantiate_edge :
		int ref -> int -> 'f term -> 'f term -> (int * 'f Subst.t) list =
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


		method output_sym_graph :
		'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "Symbol transition graph:";
			pr#enter 4;
			let collapsable = ref [] in
			let stable = ref [] in
			let iterer (f:#sym_detailed) =
				if f#is_defined then begin
					if SymG.mem_edge sym_g f#name "" then begin
						collapsable := f :: !collapsable;
					end else begin
						let succ = SymG.succ sym_g f#name in
						if succ = [] then begin
							stable := f :: !stable;
						end else begin
							pr#endl;
							f#output pr;
							pr#puts "\t-->";
							List.iter
								(fun gname -> pr#putc ' '; pr#puts gname;) succ;
						end;
					end;
				end;
			in
			trs#iter_syms iterer;
			pr#leave 2;
			pr#endl;
			pr#puts "Collapsable symbols: {";
			List.iter (fun (f : #sym) -> pr#putc ' '; f#output pr;) !collapsable;
			pr#puts " }";
			pr#endl;
			pr#puts "Stable symbols: {";
			List.iter (fun (f : #sym) -> pr#putc ' '; f#output pr;) !stable;
			pr#puts " }";
			pr#leave 2;
			pr#endl;
	end;;

