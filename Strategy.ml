open Util
open Txtr
open Io

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

let weight name temps = (name,temps)

let sum_weight mono =
  weight "Sum" [Pos, SumArgs(if mono then Arg(-1,0) else Var Bool *? Arg(-1,0)) +? Var Pos]
let mono_bpoly_weight =
  weight "poly" [Pos, SumArgs(Choice[Const 2; Const 1] *? Arg(-1,0)) +? Var Pos]
let max_weight mono =
  weight "Max" [
    Pos, ArityChoice(function
      | 0 -> Var Pos
      | _ -> MaxArgs(if mono then Arg(-1,0) else Var Bool *? Arg(-1,0) +? Var Pos)
    )
  ]
let neg_sum_weight =
  weight "NegSum" [
    Pos, ArityChoice(function
      | 0 -> Var Pos
      | _ -> Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0]
    )
  ]
let neg_max_weight =
  weight "NegMax" [
    Pos, ArityChoice(function
      | 0 -> Var Pos
      | _ -> Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0]
    )
  ]
let max_sum_weight mono maxarity =
  let arg = if mono then Arg(-1,0) else Var Bool *? Arg(-1,0) in
  weight "MaxSum" [
    Pos, ArityChoice(function
      | 0 -> Var Pos
      | 1 -> arg +? Var Pos
      | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
        MaxArgs(arg +? Var Pos)
      | _ -> Choice[SumArgs(arg) +? Var Pos; MaxArgs(arg +? Var Pos);]
    )
  ]
let neg_max_sum_weight maxarity =
  weight "NegMaxSum" [
    Pos, ArityChoice(function
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
let bmat_weight mono dim =
  let entry =
    if mono then
      fun j -> if j = 0 then Choice[Const 2; Const 1] else Var Bool
    else fun _ -> Var Bool
  in
  weight (string_of_int dim ^ "D-Mat") (
    List.init dim (fun _ ->
      (Pos, SumArgs(Sum(List.init dim (fun j -> entry j *? Arg(-1,j)))) +? Var Pos)
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
  element "min" (many ~minOccurs:1 exp_element >>= fun ss -> return (Min ss)) <|>
  element "var" (range_attribute >>= fun r -> return (Var r)) <|>
  element "choice" (many ~minOccurs:1 exp_element >>= fun ss -> return (Choice ss)) <|>
  element "arg" (
    default (-1) (int_attribute "index") >>= fun i ->
    default 0 (int_attribute "coord") >>= fun j ->
    return (Arg(i,j))
  ) <|>
  element "args" (
    default "sum" (validated_attribute "mode" "sum|max") >>= fun mode -> exp_element >>= fun s ->
    return (match mode with "max" -> MaxArgs s | _ -> SumArgs s)
  )
) xmls

let template_seq =
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

let template_entry_element =
  element "entry" (
    range_attribute >>= fun r ->
    template_seq >>= fun t ->
    return (r,t)
  )

let weight_element mono =
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
    default false (bool_attribute "neg") >>= fun neg ->
    default 3 (int_attribute "maxArity") >>= fun m ->
    return (if neg then neg_max_sum_weight m else max_sum_weight mono m)) <|>
  element "matrix" (
    mandatory (int_attribute "dim") >>= fun dim ->
    return (bmat_weight mono dim)
  ) <|>
  element "template" (
    mandatory (attribute "name") >>= fun name ->
    ( many template_entry_element <|>
      (template_seq >>= fun s -> return [Pos,s])
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
type reset_mode =
| RESET_reboot
| RESET_reset
type smt_tool = string * string list

type order_params = {
  mutable dp : bool;
  mutable w_name : string;
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
  w_name = "?";
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
  smt_tool = z3cmd;
  reset_mode = RESET_reset;
  use_scope = true;
  use_scope_ratio = 0;
  remove_all = false;
  linear = true;
  peek_in = false;
  peek_out = false;
  peek_to = stderr;
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

let smt_element =
  element "smt" (
    element "command" string >>= fun cmd ->
    many (element "arg" string) >>= fun args ->
    return (cmd,args)
  ) <|>
  element "z3" (return z3cmd) <|>
  element "cvc4" (return cvc4cmd)

let order_element dp =
  element "order" (
    default PREC_none (
      validated_attribute "precedence" "none|quasi|strict" >>= fun str ->
      return (match str with "quasi" -> PREC_quasi | "strict" -> PREC_strict | _ -> PREC_none)
    ) >>= fun prec ->
    default S_empty (
      validated_attribute "status" "none|partial|total|empty" >>= fun str ->
      return (match str with "none" -> S_none | "partial" -> S_partial | "total" -> S_total | _ -> S_empty)
    ) >>= fun status ->
    default (dp && status <> S_empty) (bool_attribute "collapse") >>= fun collapse ->
    default dp (bool_attribute "usable") >>= fun usable ->
    default z3cmd smt_element >>= fun smt ->
    default ("no weight",[]) (weight_element dp) >>= fun (w_name,w_templates) ->
    return {order_default with
      dp = dp;
      w_name = w_name;
      w_templates = Array.of_list w_templates;
      prec_mode = prec;
      status_mode = status;
      ext_lex = (match status with S_partial | S_total -> true | _ -> false);
      collapse = collapse;
      usable = usable;
      smt_tool = smt;
    }
  )

let strategy_element =
  element "strategy" (
    many (order_element false) >>= fun pre ->
    default false (element "freezing" (return true)) >>= fun freezing ->
    optional (
      element "edg" (return ()) >>= fun _ ->
      many (order_element true) >>= fun post ->
      default 0 (element "loop" (int_attribute "steps" >>= return)) >>= fun loop ->
      return (post,loop)
    ) >>= fun rest ->
    return (pre,freezing,rest)
  )

let of_string = Txtr.parse_string strategy_element
let of_file = Txtr.parse_file strategy_element
