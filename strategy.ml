open Util
open Txtr
open Io

type range = Pos | Bool | Full | Neg | Arctic

type template =
| Const of int
| Prod of template list
| Sum of template list
| Max of template list
| Min of template list
| Var of range
| Choice of template list
| Arg of int * int
| ProdArgs of template
| SumArgs of template
| MaxArgs of template
| Heuristic1 of template * template
| ArityChoice of (int -> template)

let ( *?) s t = Prod[s;t]
let (+?) s t = Sum[s;t]

type order_mode =
| O_strict
| O_weak
| O_equal

let weight name temps = (name,temps)

let arg mono x = if mono then x else Var Bool *? x

let no_weight = weight "no weight" []
let sum_weight ~mono =
	weight "Sum" [Pos, O_strict, SumArgs(arg mono (Arg(-1,0))) +? Var Pos]
let mono_bpoly_weight =
	weight "poly" [Pos, O_strict, SumArgs(Choice[Const 2; Const 1] *? Arg(-1,0)) +? Var Pos]
let max_weight ~mono =
	weight "Max" [
		Pos, O_strict, ArityChoice(function
			| 0 -> Var Pos
			| 1 -> arg mono (Arg (0,0)) +? Var Pos
			| _ -> MaxArgs(arg mono (Arg(-1,0) +? Var Pos))
		)
	]
let neg_sum_weight =
	weight "NegSum" [
		Pos, O_strict, ArityChoice(function
			| 0 -> Var Pos
			| _ -> Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0]
		)
	]
let neg_max_weight =
	weight "NegMax" [
		Pos, O_strict, ArityChoice(function
			| 0 -> Var Pos
			| _ -> Max[MaxArgs(Var Bool *? (Arg(-1,0) +? Var Full)); Const 0]
		)
	]
let max_sum_weight ?(maxarity=0) ~simp =
	weight "MaxSum" [
		Pos, O_strict, ArityChoice(function
			| 0 -> Var Pos
			| 1 -> arg simp (Arg(-1,0)) +? Var Pos
			| _ -> Heuristic1(SumArgs(arg simp (Arg(-1,0))) +? Var Pos, MaxArgs(arg simp (Arg(-1,0) +? Var Pos)))
(*
			| i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
				MaxArgs(arg +? Var Pos)
			| _ -> Choice[SumArgs(arg) +? Var Pos; MaxArgs(arg +? Var Pos);]
*)
		)
	]
let neg_max_sum_weight ~maxarity =
	weight "NegMaxSum" [
		Pos, O_strict, ArityChoice(function
			| 0 -> Var Pos
			| 1 -> Max[(Var Bool *? Arg(0,0)) +? Var Full; Const 0]
			| _ -> Heuristic1(
				Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0],
				Max[MaxArgs(Var Bool *? (Arg(-1,0) +? Var Full)); Const 0]
			)
(*
			| i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
				Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0]
			| _ -> Choice[
					Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0];
					Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0];
				]
*)
		)
	]

let bmat_weight ~mono ~simp ~dim =
	let entry j =
		(if simp || (mono && j = 0) then (debug (puts "hoa"); Choice[Const 2; Const 1]) else Var Bool) *? Arg(-1,j)
	in
	weight (string_of_int dim ^ "D-Mat") (
		List.init dim (fun j ->
			(Pos, (if j = 0 then O_strict else O_weak), SumArgs(Sum(List.init dim entry)) +? Var Pos)
		)
	)

let range_attribute =
	default Pos (
		validated_attribute "range" "pos|neg|bool|full" >>= fun s ->
		return (match s with "full" -> Full | "neg" -> Neg | "bool" -> Bool | _ -> Pos)
	)
let rec exp_element xmls = (
	element "const" (int >>= fun i -> return (Const i)) <|>
	element "sum" (many exp_element >>= fun ss -> return (Sum ss)) <|>
	element "prod" (many exp_element >>= fun ss -> return (Prod ss)) <|>
	element "max" (many ~minOccurs:1 exp_element >>= fun ss -> return (Max ss)) <|>
	element "bot" (return (Max [])) <|>
	element "min" (many ~minOccurs:1 exp_element >>= fun ss -> return (Min ss)) <|>
	element "var" (range_attribute >>= fun r -> return (Var r)) <|>
	element "choice" (many ~minOccurs:1 exp_element >>= fun ss -> return (Choice ss)) <|>
	element "heuristic" (validated_attribute "mode" "maxsum" >>= fun m ->
		exp_element >>= fun s ->
		exp_element >>= fun t ->
		return (Heuristic1(s,t))
	) <|>
	element "arg" (
		default (-1) (int_attribute "index") >>= fun i ->
		default 0 (int_attribute "coord") >>= fun j ->
		return (Arg(i,j))
	) <|>
	element "args" (
		default "sum" (validated_attribute "mode" "sum|max|prod") >>= fun mode ->
		exp_element >>= fun s ->
		return (match mode with "max" -> MaxArgs s | "prod" -> ProdArgs s | _ -> SumArgs s)
	)
) xmls

let exp_seq =
	many (
		element "case" (
			mandatory (int_attribute "arity") >>= fun a ->
			exp_element >>= fun s ->
			return (a,s)
		)
	) >>= fun ass ->
	exp_element >>= fun d ->
	let f a = match List.assoc_opt a ass with Some s -> s | None -> d in
	return (ArityChoice f)

let template_entry_element i =
	element "entry" (
		range_attribute >>= fun r ->
		default (if i = 0 then O_strict else O_weak) (
			validated_attribute "order" "strict|weak|equal" >>= fun str ->
			return (match str with
				| "strict" -> O_strict
				| "weak" -> O_weak
				| _ -> O_equal
			)
		) >>= fun ord ->
		exp_seq >>= fun t ->
		return (r,ord,t)
	)

let weight_element ~mono ~simp =
	element "poly" (return (mono_bpoly_weight)) <|>
	element "sum" (
		default false (bool_attribute "neg") >>= fun neg ->
		return (if neg then neg_sum_weight else sum_weight mono)
	) <|>
	element "max" (
		default false (bool_attribute "neg") >>= fun neg ->
		return (if neg then neg_max_weight else max_weight mono)
	) <|>
	element "maxSum" (
		if mono && not simp then fatal (puts "not allowed in rule removal") else
		default false (bool_attribute "neg") >>= fun neg ->
		default 4 (int_attribute "maxArity") >>= fun m ->
		return (if neg then neg_max_sum_weight ~maxarity:m else max_sum_weight ~maxarity:m ~simp)) <|>
	element "matrix" (
		mandatory (int_attribute "dim") >>= fun dim ->
		return (bmat_weight mono simp dim)
	) <|>
	element "template" (
		mandatory (attribute "name") >>= fun name ->
		( many_i ~minOccurs:1 template_entry_element <|> (exp_seq >>= fun s -> return [Pos,O_strict,s])
		) >>= fun ss ->
		return (weight name ss)
	)

type prec_mode =
| PREC_none
| PREC_strict
| PREC_quasi
| PREC_partial
type status_mode =
| S_none
| S_empty
| S_partial
| S_total

type order_params = {
	smt_params : Smt.params;
	dp : bool;
	w_name : string;
	w_quantify : bool;
	w_templates : (range * order_mode * template) array;
	ext_mset : bool;
	ext_lex : bool;
	status_mode : status_mode;
	status_copy : bool;
	status_nest : int;
	prec_mode : prec_mode;
	mincons : bool;
	maxcons : bool;
	ac_w : bool;
	strict_equal : bool;
	collapse : bool;
	mutable usable : bool;
	usable_w : bool;
	use_scope : bool;
	use_scope_ratio : int;
	negcoeff : bool;
}

(* checks monotonicity *)
let nonmonotone p =
  p.dp ||
  p.collapse ||
  p.status_mode = S_partial ||
  p.status_mode = S_empty && p.prec_mode <> PREC_none

let order_params
	?(dp=true) ?(prec=PREC_none) ?(status=S_empty) ?(collapse=status<>S_empty)
	?(usable=true) ?(quantify=true) ?(negcoeff=false)
	smt (w_name,w_templates) = {
	smt_params = if quantify then { smt with quantified = true; linear = false; } else smt;
	dp = dp;
	w_name = w_name;
	w_quantify = quantify;
	w_templates = Array.of_list w_templates;
	prec_mode = prec;
	status_mode = status;
	status_nest = 0;
	status_copy = false;
	ext_lex = (match status with S_partial | S_total -> true | _ -> false);
	ext_mset = false;
	collapse = collapse;
	usable = usable;
	usable_w = false;
	mincons = false;
	maxcons = false;
	ac_w = true;
	strict_equal = false;
	use_scope = true;
	use_scope_ratio = 0;
	negcoeff = negcoeff;
}

let put_order p =
	let status =
		match p.status_mode with
		| S_partial -> "pS"
		| S_total -> "S"
		| S_empty -> "eS"
		| _ -> ""
	in
	let prec = if p.prec_mode = PREC_quasi then "Q" else "" in
	let weighted = Array.length p.w_templates > 0 in
	if p.status_mode = S_empty && p.prec_mode = PREC_none then
		puts p.w_name
	else
		puts prec <<
		puts (
			match p.ext_lex, p.ext_mset with
			| true, true -> if weighted then "WRPO" else "RPO"
			| true, false -> if weighted then "WPO" else "LPO"
			| false, true -> if weighted then "WMPO" else "MPO"
			| _ -> "???"
		) << puts status << puts (if weighted then p.w_name else "")

let order_element default_smt mono =
	element "order" (
		default PREC_none (
			validated_attribute "precedence" "none|quasi|strict" >>= fun str ->
			return (match str with "quasi" -> PREC_quasi | "strict" -> PREC_strict | _ -> PREC_none)
		) >>= fun prec ->
		default S_empty (
			validated_attribute "status" "none|partial|total|empty" >>= fun str ->
			return (match str with "none" -> S_none | "partial" -> S_partial | "total" -> S_total | _ -> S_empty)
		) >>= fun status -> (
			if mono then return false
			else default (status <> S_empty) (bool_attribute "collapse")
		) >>= fun collapse -> (
			if mono then return false
			else default true (bool_attribute "usable")
		) >>= fun usable ->
		default default_smt Smt.params_of_xml >>= fun smt ->
		default no_weight (
			weight_element ~mono:(mono && status = S_empty) ~simp:(status = S_none || status = S_total)
		) >>= fun weight ->
		return (order_params smt ~dp:(not mono) ~prec:prec ~status:status ~collapse:collapse ~usable:usable weight)
	)

let strategy_element default_smt =
	element "strategy" (
		default default_smt Smt.params_of_xml >>= fun default_smt ->
		many (order_element default_smt true) >>= fun pre ->
		default false (element "freezing" (return true)) >>= fun freezing ->
		optional (
			element "edg" (return ()) >>= fun _ ->
			many (order_element default_smt false) >>= fun post ->
			default 0 (element "loop" (int_attribute "steps" >>= return)) >>= fun loop ->
			return (post,loop)
		) >>= fun rest ->
		return (pre,freezing,rest)
	)

let of_string default_smt =
	Txtr.parse_string (strategy_element default_smt)
let of_file default_smt =
	Txtr.parse_file (strategy_element default_smt)

let default smt = (
	[order_params smt ~dp:false mono_bpoly_weight],
	true, Some ( [
		order_params smt (sum_weight ~mono:false);
		order_params smt (max_weight ~mono:false);
		order_params smt ~prec:PREC_quasi ~status:S_partial no_weight;
		order_params smt (neg_max_sum_weight ~maxarity:0);
		order_params smt ~prec:PREC_quasi ~status:S_partial (max_sum_weight ~simp:false ~maxarity:0);
		order_params smt (bmat_weight ~mono:false ~simp:false ~dim:2);
		order_params smt (weight "sum_sum_int,sum_neg" [
			(Pos, O_strict, ArityChoice(function
				| 0 -> Var Pos
				| _ -> Max[SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Full; Const 0]
			) );
			(Neg, O_weak, SumArgs(Var Bool *? Arg(-1,1)) +? Var Neg);
		]);
		order_params smt (weight "heuristic_int,sum_neg" [
			(Pos, O_strict, ArityChoice(function
				| 0 -> Var Pos
				| 1 -> Max[(Var Bool *? Arg(0,0)) +? (Var Bool *? Arg(0,1)) +? Var Full; Const 0]
				| _ -> Heuristic1 (
					Max[
						SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Full;
						Const 0
					],
					Max[
						MaxArgs(
							Max[
								Var Bool *? (Arg(-1,0) +? Var Full);
								Var Bool *? (Arg(-1,1) +? Var Full)
							]
						);
						Const 0
					]
			) ) );
			(Neg, O_weak, SumArgs(Var Bool *? Arg(-1,1)) +? Var Neg);
		]);
	], 3)
)