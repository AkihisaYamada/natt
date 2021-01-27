open Term
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
| Arity0 of t * t
| Arity1 of t * t

let mono_sum_template = Sum [SumArgs (Arg 0); PosVar]
let mono_poly_template = Sum [SumArgs (Prod [Choice [Const 2; Const 1]; Arg 0]); PosVar]
let mono_max_template = Arity0(PosVar, MaxArgs (Sum [Arg 0; PosVar]))
let mono_max_or_sum_template = Sum [MaxOrSumArgs (Arg 0); PosVar]
let sum_template = Sum [SumArgs (Choice [Const 0; Arg 0]); PosVar]
let max_template = Arity0(PosVar, Arity1(sum_template, MaxArgs(Sum [Choice [Arg 0; Const 0]; PosVar])))
let max_template2 = Arity0(PosVar, Arity1(sum_template, Max [MaxArgs(Sum [Choice [Arg 0; Const 0]; PosVar]);PosVar]))
let neg_template = Arity0(PosVar, Max [Sum [SumArgs (Choice [Arg 0; Const 0]); NegVar]; Const 0])
let max_or_sum_template = Arity0(PosVar, Arity1(sum_template, Choice[sum_template; max_template]))
let max_or_sum_heuristic_template = Sum [MaxOrSumArgs (Choice [Arg 0; Const 0]); PosVar]

let of_string =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (Const i)) <|>
    element "sum" (many sub >>= fun ss -> return (Sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (Prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (Max ss)) <|>
    element "var" (default false (bool_attribute "neg") >>= fun b -> return (if b then NegVar else PosVar)) <|>
    element "choice" (sub >>= fun s1 -> sub >>= fun s2 -> return (Choice [s1;s2])) <|>
    element "arg" (default 1 (int_attribute "coord") >>= fun i -> return (Arg i)) <|>
    element "args" (
      default "sum" (attribute "mode") >>= fun mode -> sub >>= fun s ->
      match mode with
      | "sum" -> return (SumArgs s)
      | "max" -> return (MaxArgs s)
      | "maxsum" -> return (MaxOrSumArgs s)
    ) <|>
    element "maxArgs" (sub >>= fun s -> return (MaxArgs s)) <|>
    element "maxOrSumArgs" (sub >>= fun s -> return (MaxOrSumArgs s))
  ) xmls
  in
  parse_string sub

