open Util
open Term
open Subst


type arity = Unknown | Arity of int

exception ExistsConditionalRule
exception ExistsEquation
exception UnknownTheory
exception UnknownStrategy
exception UnknownProperty
exception SymbolMissmatch;;

module Ths = StrSet
module Syms = StrSet
module Rules = IntSet

type finfo =
{
	mutable symtype : symtype;
	mutable arity : arity;
	mutable defined_by : Rules.t;
	mutable weakly_defined_by : Rules.t;
	mutable stable : bool;
}

let var_finfo =
{
	symtype = Var;
	arity = Unknown;
	defined_by = Rules.empty;
	weakly_defined_by = Rules.empty;
	stable = false;
}

let output_tbl_index os prefix (i,rule) =
	output_string os prefix;
	output_string os (string_of_int i);
	output_string os ": ";
	rule#output os;
	output_char os '\n';
	flush os;;

let output_tbl os prefix ruletbl =
	List.iter (output_tbl_index os prefix)
	(List.sort (fun (i,_) (j,_) -> i - j) (Hashtbl.fold (fun i lr l -> (i,lr)::l) ruletbl []))

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
class trs =
	object (x)
		val sym_table = Hashtbl.create 64(* the symbol table *)
		val rule_table = Hashtbl.create 256
		val mutable rule_cnt = 0
		val mutable strict_rule_cnt = 0
		val mutable ths = Ths.empty(* the set of used built-in theories *)
(* information retrieval *)
		method get_table = sym_table
		method get_size = Hashtbl.length rule_table
		method get_size_strict = strict_rule_cnt
		method get_ths = ths
(* methods for symbols *)
		method private add_sym fname =
			let finfo =
				{
					symtype = Fun;
					arity = Unknown;
					defined_by = Rules.empty;
					weakly_defined_by = Rules.empty;
					stable = true;
				}
			in
			Hashtbl.add sym_table fname finfo;
			finfo
		method get_sym fname =
			try Hashtbl.find sym_table fname with Not_found -> x#add_sym fname
		method find_sym fname =
			try Hashtbl.find sym_table fname with Not_found -> var_finfo
		method iter_syms f = Hashtbl.iter f sym_table
		method fold_syms : 'a. (string -> finfo -> 'a -> 'a) -> 'a -> 'a =
			fun f a -> Hashtbl.fold f sym_table a
		method strictly_defines fname =
			try not (Rules.is_empty (Hashtbl.find sym_table fname).defined_by)
			with Not_found -> false
		method defines fname =
			try let finfo = Hashtbl.find sym_table fname in
				not (Rules.is_empty finfo.defined_by) ||
				not (Rules.is_empty finfo.weakly_defined_by)
			with Not_found -> false
		method stable fname =
			try (Hashtbl.find sym_table fname).stable
			with Not_found -> true
		method const_term (Node(fty,fname,ss)) =
			(fty = Var || not(x#defines fname)) && List.for_all x#const_term ss
		method relative_const (Node(fty,fname,ss)) =
			(fty = Var || not(x#strictly_defines fname)) && List.for_all x#relative_const ss
(* methods for rules *)
		method find_rule = Hashtbl.find rule_table
		method iter_rules f = Hashtbl.iter f rule_table
		method for_all_rules f = hashtbl_for_all f rule_table
		method exists_rule f = hashtbl_exists f rule_table
		method fold_rules : 'a. (int -> rule -> 'a -> 'a) -> 'a -> 'a =
			fun f a -> Hashtbl.fold f rule_table a
		method private add_rule_i i rule =
			let f = root rule#l in
			let g = root rule#r in
			let finfo = x#get_sym f in
			finfo.stable <- finfo.stable && f = g;
			Hashtbl.add rule_table i rule;
			if rule#is_weak then begin
				finfo.weakly_defined_by <- Rules.add i finfo.weakly_defined_by;
			end else begin
				finfo.defined_by <- Rules.add i finfo.defined_by;
				strict_rule_cnt <- strict_rule_cnt + 1;
			end;
		method add_rule rule =
			rule_cnt <- rule_cnt + 1;
			x#add_rule_i rule_cnt rule;
		method remove_rule i =
			let rule = Hashtbl.find rule_table i in
			let finfo = Hashtbl.find sym_table (root rule#l) in
			if rule#is_weak then begin
				finfo.weakly_defined_by <- Rules.remove i finfo.weakly_defined_by;
			end else begin
				finfo.defined_by <- Rules.remove i finfo.defined_by;
				strict_rule_cnt <- strict_rule_cnt - 1;
			end;
			Hashtbl.remove rule_table i;
		method replace_rule i lr =
			x#remove_rule i;
			x#add_rule_i i lr;
		method modify_rule i l r =
			x#replace_rule i (new rule (x#find_rule i)#strength l r)

(* input *)
		method private trans_term (Trs_ast.Term ((_,fname),ss)) =
			let finfo = x#get_sym fname in
			if finfo.arity = Unknown then
				finfo.arity <- Arity (List.length ss);
			Node(finfo.symtype, fname, List.map (x#trans_term) ss)
		method private add_rule_raw =
			function
			| Trs_ast.Rew ([],l,r)		-> x#add_rule (rule (x#trans_term l) (x#trans_term r));
			| Trs_ast.RelRew ([],l,r)	-> x#add_rule (weak_rule (x#trans_term l) (x#trans_term r));
			| _ 				-> raise ExistsConditionalRule
		method private add_eq_raw (l,r) =
			let l = x#trans_term l in
			let r = x#trans_term r in
			x#add_rule (weak_rule l r);
			x#add_rule (weak_rule r l);
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
			output_tbl os "    " rule_table;
		method output_last_rule os =
			output_tbl_index os "   " (rule_cnt, Hashtbl.find rule_table rule_cnt);
		method output os =
			x#output_ths os;
			x#output_rules os;
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
			let iterer_rule _ rule =
				output_string os "\t";
				rule#output os;
				output_string os "\n";
			in
			x#iter_rules iterer_rule;
			output_string os ")\n";
		method output_xml_rules os =
			output_string os "<rules>";
			x#iter_rules (fun _ rule -> rule#output_xml os);
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

	end;;

type path = int * (int list)

let path_append (c1,is1) (c2,is2) = (c1 + c2, is1 @ is2)
let cu_append (c1,u1) (c2,u2) = (c1 + c2, u1#compose u2)

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


