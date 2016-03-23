open Util
open Term
open Subst
open Io

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

class sym_detailed (f:#sym) =
	object (x:'a)
		inherit sym f#ty f#name
		val mutable arity = if f#is_var then Arity 0 else Unknown
		val mutable defined_by = Rules.empty
		val mutable weakly_defined_by = Rules.empty
		method arity_is_unknown = arity = Unknown
		method set_arity a = arity <- Arity a
		method arity =
			match arity with
			| Arity a -> a
			| _ -> raise (No_support ("arity for " ^ f#name ^ " is unknown"))
		method defined_by = defined_by
		method define_by i = defined_by <- Rules.add i defined_by
		method undefine_by i = defined_by <- Rules.remove i defined_by
		method is_defined = not (Rules.is_empty defined_by)
		method weakly_defined_by = weakly_defined_by
		method weakly_define_by i = weakly_defined_by <- Rules.add i weakly_defined_by
		method weakly_undefine_by i = weakly_defined_by <- Rules.remove i weakly_defined_by
		method is_weakly_defined = x#is_defined || not (Rules.is_empty weakly_defined_by)
		method is_const = not x#is_weakly_defined
	end;;

let output_tbl_index (pr : #Io.printer) prefix (i, (rule : #sym rule)) =
	pr#output_string "  ";
	pr#output_string prefix;
	pr#output_int i;
	pr#output_string ": ";
	rule#output pr;
	pr#cr;;

let output_tbl (pr : #Io.printer) prefix ruletbl =
	List.iter (output_tbl_index pr prefix)
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
class ['f] trs =
	object (x)
		val sym_table = Hashtbl.create 64(* the symbol table *)
		val rule_table : (int, (#sym as 'f) rule) Hashtbl.t = Hashtbl.create 256
		val mutable rule_cnt = 0
		val mutable strict_rule_cnt = 0
		val mutable ths = Ths.empty(* the set of used built-in theories *)
(* information retrieval *)
		method get_size = Hashtbl.length rule_table
		method get_size_strict = strict_rule_cnt
		method get_ths = ths
		method is_theoried = not (Ths.is_empty ths)
(* methods for symbols *)
		method private add_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				let f' = new sym_detailed f in
				Hashtbl.add sym_table f#name f';
				if f#is_var then f'#set_arity 0;
				f'
		method get_sym_name name =
			try Hashtbl.find sym_table name
			with Not_found -> x#add_sym (new sym Fun name)
		method find_sym_name name =
			try Hashtbl.find sym_table name
			with Not_found -> new sym_detailed (new sym Fun name)
		method get_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				if f#is_var then new sym_detailed f else
				try Hashtbl.find sym_table f#name with Not_found -> x#add_sym f
		method find_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				try Hashtbl.find sym_table f#name with Not_found -> new sym_detailed f
		method iter_syms iterer = Hashtbl.iter (fun _ -> iterer) sym_table
		method fold_syms : 'b. (sym_detailed -> 'b -> 'b) -> 'b -> 'b =
			fun folder acc ->
				Hashtbl.fold (fun _ -> folder) sym_table acc
		method strictly_defines_name name =
			try not (Rules.is_empty (Hashtbl.find sym_table name)#defined_by)
			with Not_found -> false
		method strictly_defines : 'b. (#sym as 'b) -> bool =
			fun f -> f#is_fun && x#strictly_defines_name f#name
		method defines : 'b. (#sym as 'b) -> bool =
			fun f ->
				f#is_fun &&
				try let f = Hashtbl.find sym_table f#name in
					f#is_defined || f#is_weakly_defined
				with Not_found -> false
		method const_term : 'b. (#sym as 'b) term -> bool =
			fun (Node(f,ss)) ->
				not (x#defines f) && List.for_all x#const_term ss
		method relative_const : 'b. (#sym as 'b) term -> bool =
			fun (Node(f,ss)) ->
				not (x#strictly_defines f) && List.for_all x#relative_const ss
(* methods for rules *)
		method find_rule = Hashtbl.find rule_table
		method iter_rules f = Hashtbl.iter f rule_table
		method for_all_rules f = hashtbl_for_all f rule_table
		method exists_rule f = hashtbl_exists f rule_table
		method fold_rules : 'b. (int -> 'f rule -> 'b -> 'b) -> 'b -> 'b =
			fun f a -> Hashtbl.fold f rule_table a
		method private add_rule_i i rule =
			let f = x#get_sym (root rule#l) in
			Hashtbl.add rule_table i rule;
			if rule#is_weak then begin
				f#weakly_define_by i;
			end else begin
				f#define_by i;
				strict_rule_cnt <- strict_rule_cnt + 1;
			end;
		method add_rule rule =
			rule_cnt <- rule_cnt + 1;
			x#add_rule_i rule_cnt rule;
		method remove_rule i =
			let rule = Hashtbl.find rule_table i in
			let f = x#get_sym (root rule#l) in
			if rule#is_weak then begin
				f#weakly_undefine_by i;
			end else begin
				f#undefine_by i;
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
			let f = x#get_sym_name fname in
			if f#arity_is_unknown then f#set_arity (List.length ss);
			Node( (f :> sym), List.map (x#trans_term) ss)
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
				List.iter (fun (_,name) -> ignore (x#add_sym (new sym (Th th) name))) syms
		method private add_decl =
			Trs_ast.(function 
			| VarDecl xs		->
				List.iter (fun (_,name) -> ignore (x#add_sym (new sym Var name))) xs
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
		method output_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			let iterer_th th =
				pr#output_string th;
				pr#output_string " symbols:";
				let iterer_syms (f:#sym) =
					if f#ty = Th th then begin
						pr#output_char ' ';
						f#output pr;
					end;
				in
				x#iter_syms iterer_syms;
				pr#cr;
			in
			Ths.iter iterer_th ths;
		method output_rules : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			output_tbl pr "    " rule_table;
		method output_last_rule : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			output_tbl_index pr "   " (rule_cnt, Hashtbl.find rule_table rule_cnt);
		method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			x#output_ths pr;
			x#output_rules pr;
		method output_wst : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#output_string "(VAR";
			let iterer_var (v : #sym) =
				if v#is_var then begin
					pr#output_char ' ';
					v#output pr;
				end
			in
			x#iter_syms iterer_var;
			pr#output_char ')';
			pr#cr;
			pr#output_string "(RULES";
			pr#enter 4;
			let iterer_rule _ (rule : #sym rule) =
				pr#cr;
				rule#output pr;
			in
			x#iter_rules iterer_rule;
			pr#output_char ')';
			pr#leave 4;
			pr#cr;
		method output_xml_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			let iterer_A (f:#sym) =
				match f#ty with
				| Th "AC" | Th "A" -> Xml.enclose "name" f#output_xml pr
				| _ -> ()
			in
			let iterer_C (f:#sym) =
				match f#ty with
				| Th "AC" | Th "C" -> Xml.enclose "name" f#output_xml pr
				| _ -> ()
			in
			Xml.enclose "Asymbols" (fun _ -> x#iter_syms iterer_A) pr;
			Xml.enclose "Csymbols" (fun _ -> x#iter_syms iterer_C) pr;
		method output_xml_rules : 'a. (#Io.printer as 'a) -> unit =
			Xml.enclose "rules" (fun pr -> x#iter_rules (fun _ rule -> rule#output_xml pr))
		method output_xml : 'a. (#Io.printer as 'a) -> unit =
			Xml.enclose "trs" x#output_xml_rules << x#output_xml_ths

		method output_xml_ho_signature : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			Xml.enter "higherOrderSignature" pr;
			let first = ref true in
			let iterer_var (v:#sym) =
				if v#is_var then begin
					if !first then begin
						Xml.enter "variableTypeInfo" pr;
						first := false;
					end;
					Xml.enclose "varDeclaration" (
						v#output_xml <<
						Xml.enclose "type" (Xml.enclose "basic" (puts "o"))
					) pr;
				end;
			in
			x#iter_syms iterer_var;
			if not !first then
				Xml.leave "variableTypeInfo" pr;
			first := true;
			let iterer_fun (f:#sym) =
				if f#is_fun then begin
					if !first then begin
						Xml.enter "functionSymbolTypeInfo" pr;
						first := false;
					end;
					Xml.enter "funcDeclaration" pr;
					f#output_xml pr;
					Xml.enter "typeDeclaration" pr;
					for i = 0 to f#arity do
						Xml.enclose "type" (Xml.enclose "basic" (putc 'o')) pr;
					done;
					Xml.leave "typeDeclaration" pr;
					Xml.leave "funcDeclaration" pr;
				end;
			in
			x#iter_syms iterer_fun;
			if not !first then begin
				Xml.leave "functionSymbolTypeInfo" pr;
			end;
			Xml.leave "higherOrderSignature" pr;
		method output_xml_ho : 'a. (#Io.printer as 'a) -> unit =
			Xml.enclose "trs" ( x#output_xml_rules << x#output_xml_ho_signature )
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


