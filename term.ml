open Util
open Params
open Io

type 'a term = Node of 'a * 'a term list

type symtype = Var | Fun | Th of string | Special

type ('a,'b) wterm = WT of 'a * ('a,'b) wterm list * 'b

let put_name name (pr:#Io.outputter) =
	let n = String.length name in
	let rec sub i =
		if i < n then begin
			match name.[i] with
			| '\\' -> pr#output_string "\\\\"; sub (i+1);
			| '#' -> pr#output_string "\\#"; sub (i+1);
			| '^' -> pr#output_string "\\^"; sub (i+1);
			| ' ' -> pr#output_char name.[i+1]; sub (i+2);
			| c -> pr#output_char c; sub (i+1);
		end;
	in
	sub 0

class sym ty0 name0 =
	object (x:'x)
		val mutable ty = ty0
		val mutable name = name0
		method is_var = ty = Var
		method is_fun = not x#is_var
		method is_theoried = match ty with Th _ -> true | _ -> false
		method is_associative = ty = Th "AC" || ty = Th "A"
		method is_commutative = ty = Th "AC" || ty = Th "C"
		method ty = ty
		method set_ty ty' = ty <- ty'
		method name = name
		method equals : 'b. (<name:string;..> as 'b) -> bool = fun y ->
			name = y#name
		method output : 'b. (#outputter as 'b) -> unit = put_name name
		method output_xml : 'b. (#printer as 'b) -> unit =
			if x#is_var then Xml.enclose_inline "var" x#output
			else Xml.enclose_inline "name" x#output
	end;;

let root (Node(f,_)) = f
let get_weight (WT(_,_,ws)) = ws
let rec erase (WT(f,ss,_)) = Node(f,List.map erase ss)

let size : 'a term -> int =
	let rec sub1 ret (Node(_,ss)) = sub2 (ret+1) ss
	and sub2 ret ss =
		match ss with
		| [] -> ret
		| s::ss -> sub2 (sub1 ret s) ss
	in
	sub1 0


let var vname = Node(new sym Var vname, [])
let app f args = Node(f, args)

(* equality *)
let rec term_eq (Node(f,ss) : #sym term) (Node(g,ts)) =
	f#equals g && List.for_all2 term_eq ss ts

let rec wterm_eq (WT((f:#sym),ss,sw)) (WT(g,ts,tw)) =
	f#equals g && List.for_all2 wterm_eq ss ts

let rec strict_subterm (s:#sym term) (Node(_,ts)) =
	List.exists (subterm s) ts
and subterm (s:#sym term) t = term_eq s t || strict_subterm s t

(* embeding relation *)
let rec emb_le (Node((f:#sym),ss) as s) (Node(g,ts) as t) =
	term_eq s t || List.exists (emb_le s) ts || f#equals g && List.for_all2 emb_le ss ts

(* the list of variable occurences in a term *)
let varlist =
	let rec sub (Node((f:#sym),ss)) =
		if f#is_var then f :: sublist ss else sublist ss
	and sublist =
		function
		| []	-> []
		| s::ss	-> sub s @ sublist ss
	in
	sub

let rec list_remove f =
	function
	| []	-> raise Not_found
	| x::xs	-> if f x then xs else x :: list_remove f xs

let dupvarlist =
	let rec sub ret (Node((f:#sym),ts)) =
		if f#is_var then
			let lvars, dupvars = ret in
			(	try
					(list_remove f#equals lvars, dupvars)
				with
				| Not_found -> (lvars, f::dupvars)
			)
		else sublist ret ts
	and sublist ret =
		function
		| []	-> ret
		| t::ts	-> sublist (sub ret t) ts
	in
	fun l r ->
		let lvars, dupvars = sub (varlist l, []) r in
		dupvars
let duplicating l r = dupvarlist l r <> []

(* the set of variables in a term *)
module VarSet = Set.Make(String)
let varset =
	let rec sub (Node((f:#sym),ts)) =
		if f#is_var then VarSet.add f#name (sublist ts) else sublist ts
	and sublist =
		function
		| []	-> VarSet.empty
		| t::ts	-> VarSet.union (sub t) (sublist ts)
	in
	sub

(* flat AC symbols *)
let rec flat =
	let rec sub (f:#sym) ss =
		function
		| []	-> Node(f, List.rev ss)
		| (Node(g,ts) as t)::us ->
			if f#equals g then
				sub f ss (ts@us)
			else
				sub f (flat t :: ss) us
	in
	fun (Node(f,ss)) ->
		match f#ty with
		| Th "AC"	-> sub f [] ss
		| _			-> Node(f, List.map flat ss)

(* flat top $f$ from list of functions *)
let local_flat (f:#sym) =
	let rec sub ss =
		function
		| [] -> ss
		| (Node(g,ts) as t)::us ->
			if f#equals g then sub ss (ts @ us) else sub (ss@[t]) us
	in
	sub []

(* unflat *)
let fold f =
	let rec sub ret =
		function
		| [] -> ret
		| s::ss -> sub (Node(f,[ret;s])) ss
	in
	function
	| [] -> failwith "bug"
	| s::ss -> sub s ss

(* top-AC subterms, for KT98 *)
let top_ac_subterms (Node(f,ss) as s) =
	if f#ty = Th "AC" then
		let args = local_flat f ss in
		let subargs = subsequences args in
		List.map (fold f) (List.filter (fun ts -> List.length ts > 1) subargs)
	else [s]

let escape c = " " ^ String.make 1 c

(* printers *)
let rec output_term (pr : #Io.outputter) : (#sym as 'a) term -> unit =
	let rec sub =
		function
		| []	-> pr#output_char ')'
		| t::ts -> pr#output_char ','; output_term pr t; sub ts
	in
	fun (Node(f,ts)) ->
		f#output pr;
		match ts with
		| []	-> if f#is_fun then pr#output_string "()";
		| t::ts	-> pr#output_char '('; output_term pr t; sub ts

let prerr_term t = output_term Io.cerr t
let prerr_terms ts = List.iter (fun t -> prerr_term t; prerr_string "  ") ts
let prerr_wterm wt = prerr_term (erase wt)
let prerr_wterms wts = List.iter (fun wt -> prerr_wterm wt; prerr_string " ") wts

(* xml printers *)
let rec output_xml_term (pr : #Io.outputter) : (#sym as 'a) term -> unit =
	let rec sub =
		function
		| []	-> Xml.leave "arg" pr; Xml.leave "funapp" pr;
		| t::ts -> Xml.leave "arg" pr; Xml.enter "arg" pr; output_xml_term pr t; sub ts
	in
	fun (Node(f,ts)) ->
		if f#is_var then begin
			f#output_xml pr;
		end else begin
			Xml.enter "funapp" pr;
			f#output_xml pr;
			match ts with
			| []	-> if f#is_fun then Xml.leave "funapp" pr;
			| t::ts	-> Xml.enter "arg" pr; output_xml_term pr t; sub ts
		end

(*** rules ***)
type strength = StrictRule | MediumRule | WeakRule

class ['a] rule s (l : (#sym as 'a) term) (r : 'a term) =
	object (x)
		val lhs : sym term = l
		val rhs : sym term = r
		val strength = s
		method l = lhs
		method r = rhs
		method strength = strength
		method size = size l + size r
		method is_strict = strength = StrictRule
		method is_medium = strength = MediumRule
		method is_weak = strength = WeakRule
		method is_duplicating = duplicating l r
		method is_size_increasing = size l < size r || x#is_duplicating
		method has_extra_variable =
			let lvars = varlist l in
			let rvars = varlist r in
			List.exists (fun rvar -> not (List.mem rvar lvars)) rvars

		method output : 'b. (#outputter as 'b) -> unit = fun pr ->
			output_term (pr :> #outputter) l;
			pr#output_string (
				match s with
				| StrictRule -> " -> "
				| WeakRule -> " ->= "
				| _ -> " ->? ");
			output_term pr r
		method output_xml : 'b. (#printer as 'b) -> unit =
			Xml.enclose "rule" (
				Xml.enclose "lhs" (fun pr -> output_xml_term pr l) <<
				Xml.enclose "rhs" (fun pr -> output_xml_term pr r)
			)
	end

let rule l r = new rule StrictRule l r
let weak_rule l r = new rule WeakRule l r
let medium_rule l r = new rule MediumRule l r

let map_rule : ((#sym as 'a) term -> 'a term) -> 'a rule -> 'a rule =
	fun f rule -> new rule rule#strength (f rule#l) (f rule#r)
