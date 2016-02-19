open Util
open Term
open Trs

(* symbol transition graph *)
module SymG = Graph.Imperative.Digraph.Concrete(StrHashed)
module SymGoper = Graph.Oper.I(SymG)


class t (trs:trs) =
	let sym_g = SymG.create () in
	let _ =
		SymG.add_vertex sym_g ""; (* this vertex represents arbitrary symbol *)
		let add_sym fname finfo =
			if finfo.symtype <> Var then begin
				SymG.add_vertex sym_g fname;
				SymG.add_edge sym_g "" fname;
			end;
		in
		trs#iter_syms add_sym;
		let add_edge _ lr =
			let Node(_,fname,_) = lr#l in
			let Node(gty,gname,_) = lr#r in
			SymG.add_edge sym_g fname (if gty = Var then "" else gname);
		in
		trs#iter_rules add_edge;
		SymGoper.add_transitive_closure sym_g;
	in
	object (x)
		method trans_sym fname gname =
			SymG.mem_edge sym_g fname "" ||
			SymG.mem_edge sym_g fname gname
(* estimations *)
		method narrows (Node(fty,fname,ss) as s) (Node(gty,gname,ts) as t) =
			fty = Var ||
			gty = Var ||
			x#is_redex_candidate s && x#trans_sym fname gname ||
			x#connects s t
		method connects (Node(fty,fname,ss)) (Node(gty,gname,ts)) =
			fname = gname &&
			(	match fty with
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
		method is_redex_candidate (Node(_,fname,ss)) =
			let tester i =
				let Node(_,_,ls) = (trs#find_rule i)#l in
				List.for_all2 x#narrows ss ls
			in
			let finfo = trs#find_sym fname in
			Rules.exists tester finfo.defined_by ||
			Rules.exists tester finfo.weakly_defined_by
		method find_matchable (Node(_,fname,_) as s) =
			let finfo = trs#find_sym fname in
			let folder i ret =
				if x#connects s (trs#find_rule i)#l then i::ret else ret
			in
			Rules.fold folder finfo.weakly_defined_by
			(Rules.fold folder finfo.defined_by [])

		method estimate_paths lim (Node(fty,_,_) as s) (Node(gty,_,_) as t) =
			if s = t || fty = Var || gty = Var then
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
		
		method instantiate_edge cnt =
			let rec sub1 lim s t =
				let paths = x#estimate_paths (min 4 lim) s t in
				List.fold_left
				(fun ret (c,is) -> let cus = instantiate_path (lim-c) s is t in List.iter (dbg s is t) cus; cus @ ret)
				[] paths
			and sub2 lim ss ts =
				match ss, ts with
				| [], [] -> [(0,new Subst.t)]
				| (s::ss), (t::ts) ->
					let mapper (c1,u1) =
						let ss' = List.map u1#subst ss in
						let ts' = List.map u1#subst ts in
						List.map (cu_append (c1,u1)) (sub2 (lim-c1) ss' ts')
					in
					List.concat (List.map mapper (sub1 lim s t))
				| _ -> []
			and instantiate_path lim (Node(fty,fname,ss) as s) is (Node(gty,gname,ts) as t) =
				match is with
				| [] ->
					if s = t then [(0,new Subst.t)]
					else if fty = Var then
						if StrSet.mem fname (varset t) then [] else [(0,Subst.singleton fname t)]
					else if gty = Var then
						if StrSet.mem gname (varset s) then [] else [(0,Subst.singleton gname s)]
					else
						(if fname = gname then
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
			fun lim (Node(_,fname,ss)) (Node(_,gname,ts)) ->
				if fname = gname then
					sub2 lim ss ts
				else
					[]


		method output_sym_graph os =
			output_string os "Symbol transition graph:\n";
			let pr g = output_char os ' '; output_name os g; in
			let collapsable = ref [] in
			let stable = ref [] in
			let iterer f finfo =
				if trs#defines f then begin
					if SymG.mem_edge sym_g f "" then begin
						collapsable := f :: !collapsable;
					end else begin
						let succ = SymG.succ sym_g f in
						if succ = [] then begin
							stable := f :: !stable;
						end else begin
							output_string os "  ";
							output_string os f;
							output_string os "\t-->";
							List.iter pr succ;
							output_char os '\n';
						end;
					end;
				end;
			in
			trs#iter_syms iterer;
			output_string os "  Collapsable symbols: {";
			List.iter pr !collapsable;
			output_string os " }\n  Stable symbols: {";
			List.iter pr !stable;
			output_string os " }\n";
	end;;

