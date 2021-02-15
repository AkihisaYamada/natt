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

let no_entry = (Pos, Const 0)
let mono_sum_template = [Pos, SumArgs(Arg(-1,0)) +? Var Pos]
let mono_bpoly_template = [Pos, SumArgs(Choice[Const 2; Const 1] *? Arg(-1,0)) +? Var Pos]
let mono_max_template =
  [Pos, ArityChoice(function 0 -> Var Pos | _ -> MaxArgs(Arg(-1,0) +? Var Pos))]
let sum_template = [Pos, SumArgs(Var Bool *? Arg(-1,0)) +? Var Pos]
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
let max_sum_template maxarity = [Pos,
  ArityChoice(function
    | 0 -> Var Pos
    | 1 -> Var Bool *? Arg(0,0) +? Var Pos
    | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
      MaxArgs(Var Bool *? Arg(-1,0) +? Var Pos)
    | _ -> Choice[
        SumArgs(Var Bool *? Arg(-1,0)) +? Var Pos;
        MaxArgs(Var Bool *? Arg(-1,0) +? Var Pos);
      ]
  )
]
let bmat_template dim =
  List.init dim (fun _ ->
    (Pos, SumArgs(Sum(List.init dim (fun j -> Var Bool *? Arg(-1,j)))) +? Var Pos)
  )

let parser =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (Const i)) <|>
    element "sum" (many sub >>= fun ss -> return (Sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (Prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (Max ss)) <|>
    element "min" (many ~minOccurs:1 sub >>= fun ss -> return (Min ss)) <|>
    element "var" (default "pos" (attribute "range") >>= fun r ->
      return (Var(match r with "bool" -> Bool | "neg" -> Neg | "full" -> Full | _ -> Pos))
    ) <|>
    element "choice" (sub >>= fun s1 -> sub >>= fun s2 -> return (Choice [s1;s2])) <|>
    element "arg" (
      default (-1) (int_attribute "index") >>= fun i ->
      default 0 (int_attribute "coord") >>= fun j ->
      return (Arg(i,j))
    ) <|>
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
    default "pos" (attribute "range") >>= fun s ->
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
    match s with
    | "pos" -> return (Pos,t)
    | "neg" -> return (Neg,t)
    | "full" -> return (Full,t)
  )
  in
  element "poly" (default false (bool_attribute "mono") >>= fun mono ->
    return (if mono then mono_bpoly_template else sum_template)
  ) <|>
  element "matrix" (
    mandatory (int_attribute "dim") >>= fun dim ->
    return (bmat_template dim)
  ) <|>
  element "multi" (many entry >>= fun ss -> return ss) <|>
  (entry >>= fun s -> return [s])

let parse_string = Txtr.parse_string parser
let parse_file = Txtr.parse_file parser
