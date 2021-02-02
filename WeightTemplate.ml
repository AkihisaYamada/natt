open Util
open Txtr

type template =
| Const of int
| Prod of template list
| Sum of template list
| Max of template list
| PosVar
| NegVar
| Choice of template list
| Arg of int
| SumArgs of template
| MaxArgs of template
| MaxOrSumArgs of template
| ArityChoice of (int -> template)

type entry = Nat of template | Int of template

let mono_sum_template = [Nat(Sum[SumArgs(Arg 0); PosVar])]
let mono_poly_template =
  [Nat(Sum[SumArgs(Prod[Choice[Const 2; Const 1]; Arg 0]); PosVar])]
let mono_max_template =
  [Nat(ArityChoice(function 0 -> PosVar | _ -> MaxArgs(Sum[Arg 0; PosVar])))]
let sum_template = [Nat(Sum[SumArgs(Choice[Arg 0; Const 0]); PosVar])]
let max_template = [Nat(
  ArityChoice(function
    | 0 -> PosVar
    | 1 -> Sum[Choice[Arg 0; Const 0]; PosVar]
    | _ -> MaxArgs(Sum[Choice[Arg 0; Const 0]; PosVar])
  )
)]
let neg_template = [Nat(
  ArityChoice(function
    | 0 -> PosVar
    | _ -> Max[Sum[SumArgs(Choice[Arg 0; Const 0]); NegVar]; Const 0]
  )
)]
let neg_max_sum_template maxarity = [Nat(
  ArityChoice(function
    | 0 -> PosVar
    | 1 -> Max[Sum[Choice[Arg 0; Const 0]; NegVar]; Const 0]
    | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
      Max[MaxArgs(Sum[Choice[Arg 0; Const 0]; NegVar]); Const 0]
    | _ -> Choice[
        Max[Sum[SumArgs(Choice[Arg 0; Const 0]); NegVar]; Const 0];
        Max[MaxArgs(Sum[Choice[Arg 0; Const 0]; NegVar]); Const 0];
      ]
  )
)]
let max_sum_template maxarity = [Nat(
  ArityChoice(function
    | 0 -> PosVar
    | 1 -> Sum[Choice[Arg 0; Const 0]; PosVar]
    | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
      MaxArgs(Sum[Choice[Arg 0; Const 0]; PosVar])
    | _ -> Choice[
        Sum[SumArgs(Choice[Arg 0; Const 0]); PosVar];
        MaxArgs(Sum[Choice[Arg 0; Const 0]; PosVar]);
      ]
  )
)]
let bmat_template dim =
  let elm = Nat(
    Sum[SumArgs(Sum(List.init dim (fun i -> Choice [Arg i; Const 0]))); PosVar]
  )
  in
  List.init dim (fun _ -> elm)

let parser =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (Const i)) <|>
    element "sum" (many sub >>= fun ss -> return (Sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (Prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (Max ss)) <|>
    element "var" (default "nat" (attribute "type") >>= fun ty -> return (match ty with "int" -> NegVar | _ -> PosVar)) <|>
    element "choice" (sub >>= fun s1 -> sub >>= fun s2 -> return (Choice [s1;s2])) <|>
    element "arg" (default 0 (int_attribute "coord") >>= fun i -> return (Arg i)) <|>
    element "args" (
      default "sum" (attribute "mode") >>= fun mode -> sub >>= fun s ->
      match mode with
      | "sum" -> return (SumArgs s)
      | "max" -> return (MaxArgs s)
      | "maxsum" -> return (MaxOrSumArgs s)
    )
  ) xmls
  in
  let entry = element "entry" (
    default "nat" (attribute "type") >>= fun s ->
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
    match s with "nat" -> return (Nat t) | "int" -> return (Int t)
  )
  in
  element "poly" (default false (bool_attribute "mono") >>= fun mono ->
    return (if mono then mono_poly_template else sum_template)
  ) <|>
  element "matrix" (
    mandatory (int_attribute "dim") >>= fun dim ->
    return (bmat_template dim)
  ) <|>
  element "multi" (many entry >>= fun ss -> return ss) <|>
  (entry >>= fun s -> return [s])

let parse_string = Txtr.parse_string parser
let parse_file = Txtr.parse_file parser
