open Util
open Txtr

type range = Pos | Bool | Full | Neg

type template =
| Const of int
| Prod of template list
| Sum of template list
| Max of template list
| Min of template list
| Var of range
| Choice of template list
| Arg of int * int
| SumArgs of template
| MaxArgs of template
| MaxOrSumArgs of template
| ArityChoice of (int -> template)

let ( *?) s t = Prod[s;t]
let (+?) s t = Sum[s;t]

let sum_template mono =
  [Pos, SumArgs(if mono then Arg(-1,0) else Var Bool *? Arg(-1,0)) +? Var Pos]
let mono_bpoly_template = [Pos, SumArgs(Choice[Const 2; Const 1] *? Arg(-1,0)) +? Var Pos]
let mono_max_template =
  [Pos, ArityChoice(function 0 -> Var Pos | _ -> MaxArgs(Arg(-1,0) +? Var Pos))]
let max_template = [Pos,
  ArityChoice(function
    | 0 -> Var Pos
    | _ -> MaxArgs(Var Bool *? Arg(-1,0) +? Var Pos)
  )
]
let neg_template = [Pos,
  ArityChoice(function
    | 0 -> Var Pos
    | _ -> Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0]
  )
]
let neg_max_sum_template maxarity = [Pos,
  ArityChoice(function
    | 0 -> Var Pos
    | 1 -> Max[Var Bool *? Arg(0,0) +? Var Full; Const 0]
    | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
      Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0]
    | _ -> Choice[
        Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0];
        Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0];
      ]
  )
]
let max_sum_template mono maxarity = [Pos,
  let arg = if mono then Arg(-1,0) else Var Bool *? Arg(-1,0) in
  ArityChoice(function
    | 0 -> Var Pos
    | 1 -> arg +? Var Pos
    | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
      MaxArgs(arg +? Var Pos)
    | _ -> Choice[SumArgs(arg) +? Var Pos; MaxArgs(arg +? Var Pos);]
  )
]
let bmat_template mono dim =
  let entry = if mono then fun j -> if j = 0 then Choice[Const 2; Const 1] else Var Bool else fun _ -> Var Bool in
  List.init dim (fun _ ->
    (Pos, SumArgs(Sum(List.init dim (fun j -> entry j *? Arg(-1,j)))) +? Var Pos)
  )

let range_attribute =
  default Pos (
    validated_attribute "range" "pos|neg|bool|full" >>= fun s ->
    return (match s with "full" -> Full | "neg" -> Neg | "bool" -> Bool | _ -> Pos)
  )

let template_element =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (Const i)) <|>
    element "sum" (many sub >>= fun ss -> return (Sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (Prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (Max ss)) <|>
    element "min" (many ~minOccurs:1 sub >>= fun ss -> return (Min ss)) <|>
    element "var" (range_attribute >>= fun r -> return (Var r)) <|>
    element "choice" (sub >>= fun s1 -> sub >>= fun s2 -> return (Choice [s1;s2])) <|>
    element "arg" (
      default (-1) (int_attribute "index") >>= fun i ->
      default 0 (int_attribute "coord") >>= fun j ->
      return (Arg(i,j))
    ) <|>
    element "args" (
      default "sum" (validated_attribute "mode" "sum|max") >>= fun mode -> sub >>= fun s ->
      return (match mode with "max" -> MaxArgs s | _ -> SumArgs s)
    )
  ) xmls
  in
  element "template" (
    range_attribute >>= fun r ->
    many (
      element "case" (
        mandatory (int_attribute "arity") >>= fun a ->
        sub >>= fun s ->
        return (a,s)
      )
    ) >>= fun ass ->
    sub >>= fun d ->
    let f a = match List.assoc_opt a ass with Some s -> s | None -> d in
    let t = ArityChoice f in
    return (r,t)
  )

let weight_element mono =
  element "poly" (return (mono_bpoly_template)) <|>
  element "sum" (return (sum_template mono)) <|>
  element "maxSum" (return (max_sum_template mono 3)) <|>
  element "matrix" (
    mandatory (int_attribute "dim") >>= fun dim ->
    return (bmat_template mono dim)
  ) <|>
  element "multi" (many template_element >>= fun ss -> return ss) <|>
  (template_element >>= fun s -> return [s])

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
type reset_mode =
| RESET_reboot
| RESET_reset
type smt_tool = string * string list

type order_params = {
  mutable dp : bool;
  mutable w_templates : (range * template) array;
  mutable base_ty : Smt.ty;
  mutable tmpvar : bool;
  mutable linear : bool;
  mutable ext_mset : bool;
  mutable ext_lex : bool;
  mutable status_mode : status_mode;
  mutable status_copy : bool;
  mutable status_nest : int;
  mutable prec_mode : prec_mode;
  mutable mincons : bool;
  mutable maxcons : bool;
  mutable ac_w : bool;
  mutable strict_equal : bool;
  mutable collapse : bool;
  mutable usable : bool;
  mutable usable_w : bool;
  mutable reset_mode : reset_mode;
  mutable use_scope : bool;
  mutable use_scope_ratio : int;
  mutable remove_all : bool;
  mutable smt_tool : smt_tool;
  mutable peek_in : bool;
  mutable peek_out : bool;
  mutable peek_to : out_channel;
}

let z3cmd = ("z3", ["-smt2";"-in"])
let cvc4cmd = ("cvc4", ["--lang=smt2"; "--incremental"; "--produce-models"])

let order_default = {
  dp = false;
  base_ty = Smt.Int;
  tmpvar = true;
  linear = true;
  w_templates = Array.make 0 (Pos, Const 0);
  ext_lex = false;
  ext_mset = false;
  status_mode = S_total;
  status_nest = 0;
  status_copy = false;
  prec_mode = PREC_quasi;
  mincons = false;
  maxcons = false;
  ac_w = true;
  strict_equal = false;
  collapse = false;
  usable = true;
  usable_w = false;
  reset_mode = RESET_reset;
  use_scope = true;
  use_scope_ratio = 0;
  remove_all = false;
  smt_tool = z3cmd;
  peek_in = false;
  peek_out = false;
  peek_to = stderr;
}

let name_order p =
  let status =
    match p.status_mode with
    | S_partial -> "pS"
    | S_total -> "S"
    | S_empty -> "eS"
    | _ -> ""
  in
  let prec =
    if p.prec_mode = PREC_quasi then "Q" else ""
  in
  if Array.length p.w_templates = 0 then
    prec ^ (
      match p.ext_lex, p.ext_mset with
      | true, true -> "RPO" ^ status
      | true, false -> "LPO" ^ status
      | false, true -> "MPO"
      | _ -> "???"
    )
  else if p.status_mode = S_empty && p.prec_mode = PREC_none then
    "Interpretation"
  else
    prec ^ "WPO" ^ status

let smt_element =
  element "smt" (
    element "command" string >>= fun cmd ->
    many (element "arg" string) >>= fun args ->
    return (cmd,args)
  ) <|>
  element "z3" (return z3cmd) <|>
  element "cvc4" (return cvc4cmd)

let order_element mono =
  element "order" (
    default PREC_none (
      validated_attribute "precedence" "none|quasi|strict" >>= fun str ->
      return (match str with "quasi" -> PREC_quasi | "strict" -> PREC_strict | _ -> PREC_none)
    ) >>= fun prec ->
    default S_empty (
      validated_attribute "status" "none|partial|total|empty" >>= fun str ->
      return (match str with "none" -> S_none | "partial" -> S_partial | "total" -> S_total | _ -> S_empty)
    ) >>= fun status ->
    default (not mono) (bool_attribute "collapse") >>= fun collapse ->
    default (not mono) (bool_attribute "usable") >>= fun usable ->
    default z3cmd smt_element >>= fun smt ->
    default [] (weight_element mono) >>= fun weight ->
    return {order_default with
      w_templates = Array.of_list weight;
      prec_mode = prec;
      status_mode = status;
      collapse = collapse;
      usable = usable;
      smt_tool = smt;
    }
  )

let strategy_element =
  element "strategy" (
    many (order_element true) >>= fun pre ->
    default false (element "freezing" (return true)) >>= fun freezing ->
    optional (
      element "edg" (return ()) >>= fun _ ->
      many (order_element false) >>= fun post ->
      default 0 (element "loop" (int_attribute "steps" >>= return)) >>= fun loop ->
      return (post,loop)
    ) >>= fun rest ->
    return (pre,freezing,rest)
  )

let of_string = Txtr.parse_string strategy_element
let of_file = Txtr.parse_file strategy_element
