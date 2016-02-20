open Util
open Params

type symtype = Var | Fun | Th of string | Special

class type sym =
	object ('a)
		inherit output
		inherit output_xml
		method is_var : bool
		method is_fun : bool
		method ty : symtype
		method name : string
	end;;
class type sym_eq =
	object
		inherit sym
		method equals : 'a. (#sym as 'a) -> bool
	end;;

let output_name os name =
	let n = String.length name in
	let rec sub i =
		if i < n then begin
			match name.[i] with
			| '\\' -> output_string os "\\\\"; sub (i+1);
			| '#' -> output_string os "\\#"; sub (i+1);
			| '^' -> output_string os "\\^"; sub (i+1);
			| ' ' -> output_char os name.[i+1]; sub (i+2);
			| c -> output_char os c; sub (i+1);
		end;
	in
	sub 0

class sym_basic ty0 name0 =
	object (x:'a)
		val mutable ty = ty0
		val name = name0
		method is_var = ty = Var
		method is_fun = ty <> Var
		method is_theoried = match ty with Th _ -> true | _ -> false
		method ty = ty
		method set_ty ty' = ty <- ty'
		method name = name
		method output os = output_name os name
		method output_xml = x#output
		method equals : 'a. (#sym as 'a) -> bool =
			fun y -> name = y#name
	end;;

type 'a term = Node of 'a * 'a term list

let root (Node(f,_)) = f

type ('a,'b) wterm = WT of 'a * ('a,'b) wterm list * 'b

let get_weight (WT(_,_,ws)) = ws
let rec erase (WT(f,ss,_)) = Node(f,List.map erase ss)

let size =
	let rec sub1 ret (Node(_,ss)) = sub2 (ret+1) ss
	and	sub2 ret ss =
		match ss with
		| [] -> ret
		| s::ss -> sub2 (sub1 ret s) ss
	in
	sub1 0

let var vname = Node(new sym_basic Var vname, [])
let app f args = Node((f:>sym_basic), args)

(* equality *)
let rec term_eq (Node(f,ss) : #sym_eq term) (Node(g,ts)) =
	f#equals g && List.for_all2 term_eq ss ts

let rec wterm_eq (WT((f:#sym_eq),ss,sw)) (WT(g,ts,tw)) =
	f#equals g && List.for_all2 wterm_eq ss ts

let rec strict_subterm (s:#sym_eq term) (Node(_,ts)) =
	List.exists (subterm s) ts
and subterm (s:#sym_eq term) t = term_eq s t || strict_subterm s t

(* embeding relation *)
let rec emb_le (Node((f:#sym_eq),ss) as s) (Node(g,ts) as t) =
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
	let rec sub ret (Node((f:#sym_eq),ts)) =
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
	let rec sub (f:#sym_eq) ss =
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
let local_flat (f:#sym_eq) =
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
let rec output_term os =
	let rec sub =
		function
		| []	-> output_string os ")"
		| t::ts -> output_string os ","; output_term os t; sub ts
	in
	fun (Node(f,ts)) ->
		f#output os;
		match ts with
		| []	-> if f#is_fun then output_string os "()";
		| t::ts	-> output_string os "("; output_term os t; sub ts
let prerr_term t = output_term stderr t
let prerr_terms ts = List.iter (fun t -> output_term stderr t; prerr_string " ") ts
let prerr_wterm wt = output_term stderr (erase wt)
let prerr_wterms wts = List.iter (fun wt -> prerr_wterm wt; prerr_string " ") wts

(* xml printers *)
let rec output_xml_term os =
	let rec sub =
		function
		| []	-> output_string os "</arg></funapp>"
		| t::ts -> output_string os "</arg><arg>"; output_xml_term os t; sub ts
	in
	fun (Node(f,ts)) ->
		if f#is_var then begin
			output_string os "<var>";
			f#output_xml os;
			output_string os "</var>";
		end else begin
			output_string os "<funapp><name>";
			f#output_xml os;
			output_string os "</name>";
			match ts with
			| []	-> if f#is_fun then output_string os "</funapp>";
			| t::ts	-> output_string os "<arg>"; output_xml_term os t; sub ts
		end

(*** rules ***)
type strength = StrictRule | MediumRule | WeakRule

class rule s (l:#sym_basic term) (r:#sym_basic term) =
	object (x)
		val lhs : sym_basic term = l
		val rhs : sym_basic term = r
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

		method output os =
			output_term os l;
			output_string os (
				match s with
				| StrictRule -> " -> "
				| WeakRule -> " ->= "
				| _ -> " ->? ");
			output_term os r
		method output_xml os =
			output_string os "<rule><lhs>";
			output_xml_term os l;
			output_string os "</lhs><rhs>";
			output_xml_term os r;
			output_string os "</rhs></rule>"
	end

let rule l r = new rule StrictRule l r
let weak_rule l r = new rule WeakRule l r
let medium_rule l r = new rule MediumRule l r

