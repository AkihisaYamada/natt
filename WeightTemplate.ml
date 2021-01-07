open Term
open Txtr

type sym =
| Const of int
| Add
| Mul
| Max
| Var
| Choice
| Arg of int
| SumArgs
| MaxArgs
| MaxOrSumArgs

let const n = Node(Const n, [])
let arg i = Node(Arg i, [])
let var = Node(Var,[])
let sum ss = Node(Add,ss)
let max ss = Node(Max,ss)
let prod ss = Node(Mul,ss)
let choice ss = Node(Choice,ss)
let sum_args s = Node(SumArgs,[s])
let max_args s = Node(MaxArgs,[s])
let max_or_sum_args s = Node(MaxOrSumArgs,[s])

let mono_sum_template = sum [sum_args (arg 0); var]
let mono_poly_template = sum [sum_args (choice [arg 0; prod [const 2; arg 0]]); var]
let mono_max_template = sum [max_args (arg 0); var]
let mono_max_or_sum_template = sum [max_or_sum_args (arg 0); var]
let sum_template = sum [sum_args (choice [arg 0; const 0]); var]
let max_template = sum [max_args (choice [arg 0; const 0]); var]
let max_or_sum_template = sum [max_or_sum_args (choice [arg 0; const 0]); var]

let of_string =
  let rec sub xmls = (
    element "const" (int >>= fun i -> return (const i)) <|>
    element "sum" (many sub >>= fun ss -> return (sum ss)) <|>
    element "prod" (many sub >>= fun ss -> return (prod ss)) <|>
    element "max" (many ~minOccurs:1 sub >>= fun ss -> return (max ss)) <|>
    element "var" (return var) <|>
    element "choice" (
      element "option" sub >>= fun s1 ->
      element "option" sub >>= fun s2 ->
      return (choice [s1;s2])
    ) <|>
    element "arg" (default 1 (int_attribute "coord") >>= fun i -> return (arg i)) <|>
    element "sumArgs" (sub >>= fun s -> return (sum_args s)) <|>
    element "maxArgs" (sub >>= fun s -> return (max_args s)) <|>
    element "maxOrSumArgs" (sub >>= fun s -> return (max_or_sum_args s))
  ) xmls
  in
  parse_string sub

