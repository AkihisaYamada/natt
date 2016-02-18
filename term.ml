open Util
open Params

type symtype = Var | Fun | Th of string | Special
type symname= string
type term = Node of symtype * symname * term list

let root (Node(_,fname,_)) = fname

type 'a wterm = WT of symtype * symname * 'a wterm list * 'a

let get_weight (WT(_,_,_,ws)) = ws
let rec erase (WT(fty,fname,ss,_)) = Node(fty,fname,List.map erase ss)

let size =
	let rec sub1 ret (Node(_,_,ss)) = sub2 (ret+1) ss
	and	sub2 ret ss =
		match ss with
		| [] -> ret
		| s::ss -> sub2 (sub1 ret s) ss
	in
	sub1 0

let var vname = Node(Var,vname,[])
let app fname args = Node(Fun,fname,args)

let rec term_rec opr (Node(fty,fname,ss)) =
	opr fty fname (List.map (term_rec opr) ss)

(* embeding relation *)
let rec emb_le (Node(fty,fname,ss) as s) (Node(gty,gname,ts) as t) =
	s = t || List.exists (emb_le s) ts || fname = gname && List.for_all2 emb_le ss ts

let rec eq (WT(fty,fname,ss,sw)) (WT(gty,gname,ts,tw)) =
	if fty = gty && fname = gname then
		List.for_all2 eq ss ts
	else
		false

let rec term_eq (Node(fty,fname,ss)) (Node(gty,gname,ts)) =
	if fty = gty && fname = gname then
		List.for_all2 term_eq ss ts
	else
		false

let rec is_strict_subterm s (Node(_,_,ts)) = List.exists (is_subterm s) ts
and is_subterm s t = s = t || is_strict_subterm s t

(* the list of variable occurences in a term *)
let varlist =
	let rec sub (Node(fty,fname,ss)) =
		match fty with
		| Var	-> fname :: sublist ss
		| _		-> sublist ss
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
	let rec sub ret (Node(fty,fname,ts)) =
		match fty with
		| Var	->
			let lvars, dupvars = ret in
			(	try
					(list_remove (fun gname -> fname = gname) lvars, dupvars)
				with
				| Not_found -> (lvars, fname::dupvars)
			)
		| _ -> sublist ret ts
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
	let rec sub (Node(fty,fname,ts)) =
		match fty with
		| Var	-> VarSet.add fname (sublist ts)
		| _		-> sublist ts
	and sublist =
		function
		| []	-> VarSet.empty
		| t::ts	-> VarSet.union (sub t) (sublist ts)
	in
	sub


let isvar_sym =
	function
	| (Var,_)	-> true
	| _			-> false

(* $\texttt{subterm}\ s\ t$ iff $s$ is a subterm of $t$ *)
let subterm s =
	let rec sub (Node(_,_,ts) as t) =
		if s = t then true else sublist ts
	and sublist =
		function
		| []	-> false
		| t::ts	-> sub t || sublist ts
	in sub

(* flat AC symbols *)
let rec flat =
	let rec sub fty fname ss =
		function
		| []	-> Node(fty, fname, List.rev ss)
		| (Node(_,gname,ts) as t)::us ->
			if gname = fname then
				sub fty fname ss (ts@us)
			else
				sub fty fname (flat t :: ss) us
	in
	fun (Node(fty,fname,ss)) ->
		match fty with
		| Th "AC"	-> sub fty fname [] ss
		| _			-> Node(fty, fname, List.map flat ss)

(* flat top $f$ from list of functions *)
let local_flat fname =
	let rec sub ss =
		function
		| [] -> ss
		| (Node(_,gname,ts) as t)::us ->
			if fname = gname then sub ss (ts @ us) else sub (ss@[t]) us
	in
	sub []

(* unflat *)
let fold fty fname =
	let rec sub ret =
		function
		| [] -> ret
		| s::ss -> sub (Node(fty,fname,[ret;s])) ss
	in
	function
	| [] -> failwith "bug"
	| s::ss -> sub s ss

(* top-AC subterms, for KT98 *)
let top_ac_subterms (Node(fty, fname, ss) as s) =
	if fty = Th "AC" then
		let args = local_flat fname ss in
		let subargs = subsequences args in
		List.map (fold fty fname) (List.filter (fun ts -> List.length ts > 1) subargs)
	else [s]

let escape c = "\x1b" ^ String.make 1 c

(* printers *)
let output_name os s =
	let n = String.length s in
	let rec sub i =
		if i < n then begin
			match s.[i] with
			| '\\' -> output_string os "\\\\"; sub (i+1);
			| '#' -> output_string os "\\#"; sub (i+1);
			| '\x1b' -> output_char os s.[i+1]; sub (i+2);
			| c -> output_char os c; sub (i+1);
		end;
	in
	sub 0

let rec output_term os =
	let rec sub =
		function
		| []	-> output_string os ")"
		| t::ts -> output_string os ","; output_term os t; sub ts
	in
	fun (Node(fty,fname,ts)) ->
		output_name os fname;
		debug (fun _ ->
			match fty with
			| Th s -> output_string os ("["^s^"]");
			| _ -> ());
		match ts with
		| []	-> if fty <> Var then output_string os "()";
		| t::ts	-> output_string os "("; output_term os t; sub ts
let prerr_term = output_term stderr
let prerr_terms = List.iter (fun t -> output_term stderr t; prerr_string " ")
let prerr_wterm wt = output_term stderr (erase wt)
let prerr_wterms wts = List.iter (fun wt -> prerr_wterm wt; prerr_string " ") wts

(* xml printers *)
let rec output_xml_term os =
	let rec sub =
		function
		| []	-> output_string os "</arg></funapp>"
		| t::ts -> output_string os "</arg><arg>"; output_xml_term os t; sub ts
	in
	fun (Node(fty,fname,ts)) ->
		if fty = Var then begin
			output_string os "<var>";
			output_string os fname;
			output_string os "</var>";
		end else begin
			output_string os "<funapp><name>";
			output_string os fname;
			output_string os "</name>";
			match ts with
			| []	-> if fty <> Var then output_string os "</funapp>";
			| t::ts	-> output_string os "<arg>"; output_xml_term os t; sub ts
		end

(*** rules ***)
type strength = StrictRule | MediumRule | WeakRule

class rule s (l:term) (r:term) =
	object (x)
		val lhs = l
		val rhs = r
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

