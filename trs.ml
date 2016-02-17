open Util
open Term
open Subst


type arity = Unknown | Arity of int
type strength = StrictRule | MediumRule | WeakRule

exception ExistsConditionalRule
exception ExistsEquation
exception UnknownTheory
exception UnknownStrategy
exception UnknownProperty
exception SymbolMissmatch;;

module Ths = StrSet
module Syms = StrSet
module Rules = IntSet

(* symbol transition graph *)
module SymG = Graph.Imperative.Digraph.Concrete(StrHashed)
module SymGoper = Graph.Oper.I(SymG)

type finfo =
{
	mutable symtype : symtype;
	mutable arity : arity;
	mutable defined_by : Rules.t;
	mutable equated_by : Rules.t;
	mutable stable : bool;
}

let var_finfo =
{
	symtype = Var;
	arity = Unknown;
	defined_by = Rules.empty;
	equated_by = Rules.empty;
	stable = false;
}

let output_tbl_index os output prefix (i,(l,r,strength)) =
	output_string os prefix;
	output_string os (string_of_int i);
	output_string os ": ";
	output os (l,r);
	begin match strength with
		| WeakRule -> output_string os "\t[weak]\n"
		| MediumRule -> output_string os "\t[medium]\n"
		| StrictRule -> output_char os '\n'
	end;
	flush os;;

let output_tbl os output prefix ruletbl =
	List.iter (output_tbl_index os output prefix)
	(List.sort (fun (i,_) (j,_) -> i - j) (Hashtbl.fold (fun i rule l -> (i,rule)::l) ruletbl []))

let hashtbl_exists test hashtbl =
	try
		Hashtbl.iter (fun l v -> if test l v then raise Success;) hashtbl;
		false
	with Success -> true

let hashtbl_for_all test hashtbl =
	try
		Hashtbl.iter (fun l v -> if not (test l v) then raise Success;) hashtbl;
		true
	with Success -> false

(* the class for TRSs *)
class t =
	object (x)
		val sym_table = Hashtbl.create 64(* the symbol table *)
		val rule_table = Hashtbl.create 256
		val sym_g = SymG.create ()(* symbol transition graph *)
		val mutable rule_cnt = 0
		val mutable strict_rule_cnt = 0
		val mutable ths = Ths.empty(* the set of used built-in theories *)
		val mutable defsyms = Syms.empty
(* information retrieval *)
		method get_table = sym_table
		method get_size = Hashtbl.length rule_table
		method get_size_strict = strict_rule_cnt
		method get_ths = ths
		method get_defsyms = defsyms
(* methods for symbols *)
		method private add_sym fname =
			let finfo =
				{
					symtype = Fun;
					arity = Unknown;
					defined_by = Rules.empty;
					equated_by = Rules.empty;
					stable = true;
				}
			in
			Hashtbl.add sym_table fname finfo;
			finfo
		method get_sym fname =
			try Hashtbl.find sym_table fname with Not_found -> x#add_sym fname
		method find_sym fname =
			try Hashtbl.find sym_table fname with Not_found -> var_finfo
		method has_constructor fname = 
			let finfo = x#find_sym fname in
			finfo.symtype <> Var && Rules.is_empty finfo.defined_by
		method defines fname =
			try not (Rules.is_empty (Hashtbl.find sym_table fname).defined_by)
			with Not_found -> false
		method stable fname =
			try (Hashtbl.find sym_table fname).stable
			with Not_found -> true
		method undefine fname i =
			let finfo = x#get_sym fname in
			finfo.defined_by <- Rules.remove i finfo.defined_by;
			if Rules.is_empty finfo.defined_by then
				defsyms <- Syms.remove fname defsyms;
		method const_term (Node(fty,fname,ss)) =
			(fty = Var || not(x#defines fname)) && List.for_all x#const_term ss
		method init_sym_graph =
			SymG.add_vertex sym_g ""; (* this vertex represents arbitrary symbol *)
			let add_sym fname finfo =
				if finfo.symtype <> Var then begin
					SymG.add_vertex sym_g fname;
					SymG.add_edge sym_g "" fname;
				end;
			in
			Hashtbl.iter add_sym sym_table;
			let add_edge _ (Node(_,fname,_),Node(gty,gname,_),_) =
				SymG.add_edge sym_g fname (if gty = Var then "" else gname);
			in
			Hashtbl.iter add_edge rule_table;
			SymGoper.add_transitive_closure sym_g;

		method trans_sym fname gname = SymG.mem_edge sym_g fname gname
(* methods for rules *)
		method find_rule = Hashtbl.find rule_table
		method find_eq i = let (l,r,_) = Hashtbl.find rule_table i in (l,r)
		method iter_rules f = Hashtbl.iter f rule_table
		method iter_rules_strict f =
			Hashtbl.iter (fun i (l,r,s) -> if s = StrictRule then f i (l,r)) rule_table
		method iter_eqs f =
			Hashtbl.iter (fun i (l,r,s) -> if s = WeakRule then f i (l,r)) rule_table
		method for_all_rules f = hashtbl_for_all f rule_table
		method for_all_rules_strict f =
			hashtbl_for_all (fun i (l,r,s) -> s <> StrictRule || f i (l,r)) rule_table
		method for_all_eqs f =
			hashtbl_for_all (fun i (l,r,s) -> s <> WeakRule || f i (l,r)) rule_table
		method exists_rule f = hashtbl_exists f rule_table
		method fold_rules : 'a. (int -> term * term * strength -> 'a -> 'a) -> 'a -> 'a =
			fun f a -> Hashtbl.fold f rule_table a
		method fold_eqs : 'a. (int -> term * term -> 'a -> 'a) -> 'a -> 'a =
			fun f a ->
				let folder i (l,r,s) aa = if s = WeakRule then f i (l,r) aa else aa in
				 Hashtbl.fold folder rule_table a
		method add_rule_extra s (Node(_,fname,_) as l) (Node(gty,gname,_) as r) =
			rule_cnt <- rule_cnt + 1;
			if s = StrictRule then strict_rule_cnt <- strict_rule_cnt + 1;
			defsyms <- Syms.add fname defsyms;
			Hashtbl.add rule_table rule_cnt (l,r,s);
			let finfo = x#get_sym fname in
			finfo.defined_by <- Rules.add rule_cnt finfo.defined_by;
			finfo.stable <- finfo.stable && fname = gname;
		method add_rule = x#add_rule_extra StrictRule;
		method add_eq = x#add_rule_extra WeakRule
		method replace_rule_extra strength i (Node(_,fname,_) as l) (Node(_,gname,_) as r) =
			let (Node(_,hname,_),_,s) = Hashtbl.find rule_table i in
			x#undefine hname i;
			if s = StrictRule then strict_rule_cnt <- strict_rule_cnt - 1;
			let finfo = x#get_sym fname in
			finfo.stable <- finfo.stable && fname = gname;
			Hashtbl.replace rule_table i (l,r,strength);
			finfo.defined_by <- Rules.add i finfo.defined_by;
			if strength = StrictRule then strict_rule_cnt <- strict_rule_cnt + 1;
		method replace_rule = x#replace_rule_extra StrictRule
		method replace_eq = x#replace_rule_extra WeakRule
		method remove_rule i =
			let (Node(_,fname,_),_,s) = Hashtbl.find rule_table i in
			x#undefine fname i;
			Hashtbl.remove rule_table i;
			if s = StrictRule then strict_rule_cnt <- strict_rule_cnt - 1;
		method remove_eq = x#remove_rule

(* input *)
		method private trans_term (Trs_ast.Term ((_,fname),ss)) =
			let finfo = x#get_sym fname in
			if finfo.arity = Unknown then
				finfo.arity <- Arity (List.length ss);
			Node(finfo.symtype, fname, List.map (x#trans_term) ss)
		method private add_rule_raw rule =
			match rule with
			| Trs_ast.Rew ([],l,r)		-> x#add_rule (x#trans_term l) (x#trans_term r);
			| Trs_ast.RelRew ([],l,r)	-> x#add_eq (x#trans_term l) (x#trans_term r);
			| _ 				-> raise ExistsConditionalRule
		method private add_eq_raw (l,r) =
			x#add_eq (x#trans_term l) (x#trans_term r);
		method private add_theory_raw =
			function
			| Trs_ast.Equations eqs -> List.iter (x#add_eq_raw) eqs
			| Trs_ast.Builtin ((_,th), syms) ->
				ths <- Ths.add th ths;
				List.iter (fun (_,f) -> (x#add_sym f).symtype <- Th th) syms
		method private add_decl =
			Trs_ast.(function 
			| VarDecl xs		-> List.iter (fun (_,v) -> (x#add_sym v).symtype <- Var) xs
			| TheoryDecl ths	-> List.iter (x#add_theory_raw) ths
			| RulesDecl rs		-> List.iter (x#add_rule_raw) rs
			| StrategyDecl _	-> ()(* raise UnknownStrategy *)
			| OtherDecl _		-> ())
		method read file =
			let c = open_in file in
			List.iter x#add_decl (Read.check_trs file c);
			close_in c
		method read_stdin =
			List.iter x#add_decl (Read.check_trs "stdin" stdin);
(* outputs *)
		method output_ths os =
			let iterer_th th =
				output_string os "  ";
				output_string os th;
				output_string os " symbols:";
				let iterer_syms fname finfo =
					if finfo.symtype = Th th then begin
						output_string os " ";
						output_string os fname;
					end;
				in
				Hashtbl.iter iterer_syms sym_table;
				output_string os "\n";
			in
			Ths.iter iterer_th ths;
		method output_rules os =
			output_tbl os output_rule "    " rule_table;
		method output_eqs os = ()
		method output_last_eq os =
			output_tbl_index os output_rule "   " (rule_cnt, Hashtbl.find rule_table rule_cnt);
		method output os =
			x#output_ths os;
			x#output_rules os;
			x#output_eqs os;
		method output_wst os =
			output_string os "(VAR";
			let iterer_var fname finfo =
				if finfo.symtype = Var then begin
					output_string os " ";
					output_string os fname;
				end
			in
			Hashtbl.iter iterer_var sym_table;
			output_string os ")\n(RULES\n";
			let iterer_rule _ (l,r,s) =
				output_string os "\t";
				begin
					match s with
					| StrictRule -> output_rule os (l,r);
					| _ -> output_eq os (l,r);
				end;
				output_string os "\n";
			in
			x#iter_rules iterer_rule;
			output_string os ")\n";
		method output_xml_rules os =
			output_string os "<rules>";
			x#iter_rules_strict (fun _ rule -> output_xml_rule os rule);
			output_string os "</rules>";
		method output_xml_ho_signature os =
			output_string os "<higherOrderSignature>";
			let first = ref true in
			let iterer_var fname finfo =
				if finfo.symtype = Var then begin
					if !first then begin
						output_string os "<variableTypeInfo>";
						first := false;
					end;
					output_string os "<varDeclaration><var>";
					output_string os fname;
					output_string os "</var><type><basic>o</basic></type></varDeclaration>";
				end;
			in
			Hashtbl.iter iterer_var sym_table;
			if not !first then
				output_string os "</variableTypeInfo>";
			first := true;
			let iterer_fun fname finfo =
				if finfo.symtype = Fun then begin
					if !first then begin
						output_string os "<functionSymbolTypeInfo>";
						first := false;
					end;
					output_string os "<funcDeclaration><name>";
					output_string os fname;
					output_string os "</name><typeDeclaration>";
					match finfo.arity with
					| Arity n ->
						for i = 0 to n do
							output_string os "<type><basic>o</basic></type>";
						done;
						output_string os "</typeDeclaration></funcDeclaration>";
					| _ -> raise (Internal "arity");
				end;
			in
			Hashtbl.iter iterer_fun sym_table;
			if not !first then
				output_string os "</functionSymbolTypeInfo>";
			output_string os "</higherOrderSignature>";
		method output_xml_ho os =
			output_string os "<trs>";
			x#output_xml_rules os;
			x#output_xml_ho_signature os;
			output_string os "</trs>";
		method output_xml os =
			output_string os "<trs>";
			x#output_xml_rules os;
			output_string os "</trs>";

(* estimations *)
		method estimate_narrow (Node(fty,fname,ss) as s) (Node(gty,gname,ts) as t) =
			fty = Var ||
			gty = Var ||
			x#is_redex_candidate s && x#trans_sym fname gname ||
			x#estimate_edge s t
		method estimate_edge (Node(fty,fname,ss)) (Node(gty,gname,ts)) =
			fname = gname &&
			(	match fty with
				| Fun -> List.for_all2 x#estimate_narrow ss ts
				| Th "C" ->
					(	match ss, ts with
						| [s1;s2], [t1;t2] ->
							(x#estimate_narrow s1 t1 && x#estimate_narrow s2 t2) ||
							(x#estimate_narrow s1 t2 && x#estimate_narrow s2 t1)
						| _ -> raise (No_support "nonbinary commutative symbol")
					)
				| _ -> true
			)
		method is_redex_candidate (Node(_,fname,ss)) =
			let rtester i =
				let (Node(_,_,ls),_,_) = x#find_rule i in
				List.for_all2 x#estimate_narrow ss ls
			in
			let etester i =
				let (Node(_,_,ls),_) = x#find_eq i in
				List.for_all2 x#estimate_narrow ss ls
			in
			Rules.exists rtester (x#find_sym fname).defined_by ||
			Rules.exists etester (x#find_sym fname).equated_by
		method find_matchable (Node(_,fname,_) as s) =
			let finfo = x#find_sym fname in
			let folder i ret =
				let (l,_,_) = x#find_rule i in
				if x#estimate_edge s l then i::ret else ret
			in
			Rules.fold folder finfo.defined_by []

	end;;

type path = int * (int list)

let path_append (c1,is1) (c2,is2) = (c1 + c2, is1 @ is2)
let cu_append (c1,u1) (c2,u2) = (c1 + c2, u1#compose u2)

let rec estimate_paths (trs:t) lim (Node(fty,_,_) as s) (Node(gty,_,_) as t) =
	if s = t || fty = Var || gty = Var then
		[(0,[])]
	else if lim > 0 then
		let init = if trs#estimate_edge s t then [(1,[])] else [] in
		let folder ret i =
			let (_,r,_) = trs#find_rule i in
			List.map (path_append (1,[i])) (estimate_paths trs (lim-1) r t) @ ret
		in
		List.fold_left folder init (trs#find_matchable s)
	else
		[]

let dbg s is t (c,u) =
()(*
prerr_endline "";
prerr_term s;
prerr_string " -";
List.iter (fun i -> prerr_int i; prerr_string ">";) is;
prerr_term t;
prerr_endline "?";
u#output stderr
*)
let instantiate_edge (trs:t) cnt =
	let rec sub1 lim s t =
		let paths = estimate_paths trs (min 4 lim) s t in
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
			let (l,r,_) = trs#find_rule i in
			let l = Subst.vrename v l in
			let r = Subst.vrename v r in
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


