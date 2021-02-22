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
| ProdArgs of template
| SumArgs of template
| MaxArgs of template
| Heuristic1 of template * template
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
      | _ -> Heuristic1(SumArgs(arg) +? Var Pos, MaxArgs(arg +? Var Pos))
(*
      | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
        MaxArgs(arg +? Var Pos)
      | _ -> Choice[SumArgs(arg) +? Var Pos; MaxArgs(arg +? Var Pos);]
*)
    )
  ]
let neg_max_sum_weight maxarity =
  weight "NegMaxSum" [
    Pos, ArityChoice(function
      | 0 -> Var Pos
      | 1 -> Max[Var Bool *? Arg(0,0) +? Var Full; Const 0]
      | _ -> Heuristic1(
        Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0],
        Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0]
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

let bmat_weight mono dim =
  let entry =
    if mono then
      fun j -> (if j = 0 then Choice[Const 2; Const 1] else Var Bool) *? Arg(-1,j)
    else fun j -> Var Bool *? Arg(-1,j)
  in
  weight (string_of_int dim ^ "D-Mat") (
    List.init dim (fun _ -> (Pos, SumArgs(Sum(List.init dim entry)) +? Var Pos))
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

let template_entry_element =
  element "entry" (
    range_attribute >>= fun r ->
    exp_seq >>= fun t ->
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
    default 4 (int_attribute "maxArity") >>= fun m ->
    return (if neg then neg_max_sum_weight m else max_sum_weight mono m)) <|>
  element "matrix" (
    mandatory (int_attribute "dim") >>= fun dim ->
    return (bmat_weight mono dim)
  ) <|>
  element "template" (
    mandatory (attribute "name") >>= fun name ->
    ( many ~minOccurs:1 template_entry_element <|> (exp_seq >>= fun s -> return [Pos,s])
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
  w_templates : (range * template) array;
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
  remove_all : bool;
  use_scope : bool;
  use_scope_ratio : int;
}

let z3cmd = "z3"
let z3args = ["-smt2";"-in"]
let cvc4cmd = "cvc4"
let cvc4args = ["--lang=smt2"; "--incremental"; "--produce-models"]

let default_smt = Smt.default_params z3cmd z3args

let default_order = {
  smt_params = default_smt;
  dp = false;
  w_name = "???";
  w_templates = Array.make 0 (Pos,Const 0);
  ext_mset = false;
  ext_lex = false;
  status_mode = S_empty;
  status_copy = false;
  status_nest = 0;
  prec_mode = PREC_none;
  mincons = false;
  maxcons = false;
  ac_w = false;
  strict_equal = false;
  collapse = false;
  usable = false;
  usable_w = false;
  remove_all = false;
  use_scope = true;
  use_scope_ratio = 0;
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
    default (false,stderr) (
      (bool_attribute "peek" >>= fun b -> return (b,stderr)) <|>
      (attribute "peekTo" >>= fun file -> return (true,open_out file))
    ) >>= fun (peek,peek_to) ->
    default false (bool_attribute "tempvars") >>= fun tmpvar ->
    default true (bool_attribute "linear") >>= fun linear ->
    ( ( element "command" string >>= fun cmd ->
        many (element "arg" string) >>= fun args ->
        return (cmd,args)
      ) <|>
      element "z3" (return (z3cmd,z3args)) <|>
      element "cvc4" (return (cvc4cmd,cvc4args))
    ) >>= fun (cmd,args) ->
    return Smt.{
      cmd = cmd;
      args = args;
      base_ty = Smt.Int;
      tmpvar = tmpvar;
      linear = linear;
      peek_in = peek;
      peek_out = peek;
      peek_to = peek_to;
    }
  )

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
    default (not mono && status <> S_empty) (bool_attribute "collapse") >>= fun collapse ->
    default (not mono) (bool_attribute "usable") >>= fun usable ->
    default default_smt smt_element >>= fun smt ->
    default ("no weight",[]) (weight_element mono) >>= fun (w_name,w_templates) ->
    return {
      smt_params = smt;
      dp = not mono;
      w_name = w_name;
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
      remove_all = false;
      use_scope = true;
      use_scope_ratio = 0;
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
