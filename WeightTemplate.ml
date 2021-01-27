open Util
open Txtr

type t =
| Const of int
| Prod of t list
| Sum of t list
| Max of t list
| PosVar
| NegVar
| Choice of t list
| Arg of int
| SumArgs of t
| MaxArgs of t
| MaxOrSumArgs of t
| ArityChoice of (int -> t)

let mono_sum_template = Sum [SumArgs (Arg 0); PosVar]
let mono_poly_template = Sum [SumArgs (Prod [Choice [Const 2; Const 1]; Arg 0]); PosVar]
let mono_max_template = ArityChoice(function 0 -> PosVar | _ -> MaxArgs (Sum [Arg 0; PosVar]))
let mono_max_sum_template = Sum [MaxOrSumArgs (Arg 0); PosVar]
let sum_template = Sum [SumArgs (Choice [Arg 0; Const 0]); PosVar]
let max_template = ArityChoice(function
  | 0 -> PosVar
  | 1 -> Sum[Choice[Arg 0; Const 0]; PosVar]
  | _ -> MaxArgs(Sum [Choice [Arg 0; Const 0]; PosVar])
)
let neg_template = ArityChoice(function
  | 0 -> PosVar
  | _ -> Max[Sum[SumArgs(Choice [Arg 0; Const 0]); NegVar]; Const 0]
)
let neg_max_sum_template maxarity = ArityChoice(function
  | 0 -> PosVar
  | 1 -> Max[Sum[Choice[Arg 0; Const 0]; NegVar]; Const 0]
  | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
    Max[MaxArgs(Sum[Choice[Arg 0; Const 0]; NegVar]); Const 0]
  | _ -> Choice[
      Max[Sum[SumArgs(Choice[Arg 0; Const 0]); NegVar]; Const 0];
      Max[MaxArgs(Sum[Choice[Arg 0; Const 0]; NegVar]); Const 0];
    ]
)
let max_sum_template maxarity = ArityChoice(function
  | 0 -> PosVar
  | 1 -> Sum[Choice[Arg 0; Const 0]; PosVar]
  | i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
    MaxArgs(Sum[Choice[Arg 0; Const 0]; PosVar])
  | _ -> Choice[
      Sum[SumArgs(Choice[Arg 0; Const 0]); PosVar];
      MaxArgs(Sum[Choice[Arg 0; Const 0]; PosVar]);
    ]
)
let bmat_template dim =
  Sum[SumArgs(Sum(List.map (fun i -> Choice [Arg i; Const 0]) (int_list 0 (dim-1)))); PosVar]


let of_string =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (Const i)) <|>
    element "sum" (many sub >>= fun ss -> return (Sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (Prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (Max ss)) <|>
    element "var" (default false (bool_attribute "neg") >>= fun b -> return (if b then NegVar else PosVar)) <|>
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
  parse_string (
    element "poly" (default false (bool_attribute "mono") >>= fun mono ->
      return [if mono then mono_poly_template else sum_template]
    ) <|>
    element "matrix" (
      mandatory (int_attribute "dim") >>= fun dim ->
      return (List.init dim (fun _ -> bmat_template dim))
    ) <|>
    element "multi" (many sub >>= fun ss -> return ss) <|>
    (sub >>= fun s -> return [s])
  )

