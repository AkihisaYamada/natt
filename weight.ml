open Sym
open Term
open Smt
open Util
open Preorder
open Params
open Io

type 'a t =
| BVar of 'a
| Smt of exp
| Prod of 'a t list
| Sum of 'a t list
| Max of 'a t list
| Cond of exp * 'a t * 'a t

let zero_w = Sum []
let one_w = Prod []

let eval_w solver =
  let rec sub w =
    match w with
    | BVar _ -> w
    | Smt e -> Smt (solver#get_value e)
    | Prod ws -> Prod (List.map sub ws)
    | Sum ws -> Sum (List.map sub ws)
    | Max ws -> Max (remdups (List.map sub ws))
    | Cond(e,w1,w2) -> (
        match solver#get_value e with
        | LB b -> sub (if b then w1 else w2)
        | e' -> Cond(e', sub w1, sub w2)
      )
  in
  fun w -> sub w

let eval_vec solver = Array.map (eval_w solver)

let refer_w solver =
  let rec sub w =
    match w with
    | BVar _ -> w
    | Smt e -> Smt (solver#refer_base e)
    | Prod ws -> Prod (List.map sub ws)
    | Sum ws -> Sum (List.map sub ws)
    | Max ws -> Max (List.map sub ws)
    | Cond(e,w1,w2) -> Cond(solver#refer Bool e, sub w1, sub w2)
  in sub

let refer_vec solver = Array.map (refer_w solver)

let put_w var =
  let paren l l' m = if l <= l' then m else putc '(' << m << putc ')' in
  let rec sub l w =
    match w with
    | BVar v -> var v
    | Smt e -> put_exp e
    | Max ws -> puts "max{ " << punct_list (sub 0) (puts ", ") ws << puts " }"
    | Sum ws -> paren l 1 (punct_list (sub 1) (puts " + ") ws)
    | Prod ws -> paren l 2 (punct_list (sub 2) (puts " * ") ws)
  in
  sub 0

let put_vec var wa : #Io.outputter -> unit = puts "[ " << punct_list (put_w var) (puts "; ") (Array.to_list wa) << puts " ]"

let eq_0_w =
  let rec sub w =
    match w with
    | BVar v -> LB false
    | Smt e -> e =^ LI 0
    | Prod ws -> smt_exists sub ws
    | Sum ws -> smt_for_all sub ws (* sound: cancellation is not considered *)
    | Max ws -> smt_for_all sub ws (* sound *)
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  in sub

let ge_0_w =
  let rec sub w =
    match w with
    | BVar v -> LB true (* carrier is assumed to be nonnegative *)
    | Smt e -> e >=^ LI 0
    | Prod ws -> LB true (* don't support negative in products *)
    | Sum ws -> smt_for_all sub ws (* sound: cancellation is not considered *)
    | Max ws -> smt_exists sub ws
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  in sub

let eq_1_w =
  let rec sub w =
    match w with
    | BVar v -> LB false
    | Smt e -> e =^ LI 1
    | Prod ws -> smt_for_all sub ws (* division is not considered *)
    | Sum ws -> LB false (* sound *)
    | Max ws -> LB false (* sound *)
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  in sub

let ge_1_w =
  let rec sub w =
    match w with
    | BVar v -> LB false
    | Smt e -> e >=^ LI 1
    | Prod ws -> smt_for_all sub ws
    | Sum ws -> sub_sum ws
    | Max ws -> smt_exists sub ws
  and sub_sum ws =
    match ws with
    | [] -> LB false
    | w::ws -> (sub w &^ smt_for_all ge_0_w ws) |^ (ge_0_w w &^ sub_sum ws)
  in sub

let const_on_w x =
  let rec sub w =
    match w with
    | BVar v -> LB (x = v)
    | Smt e -> LB true
    | Prod ws -> smt_for_all sub ws |^ smt_exists eq_0_w ws
    | Sum ws -> smt_for_all sub ws
    | Max ws -> smt_for_all sub ws
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  in sub

let is_var_w x =
  let rec sub w =
    match w with
    | BVar v -> LB(x = v)
    | Smt e -> LB false
    | Prod ws -> sub_prod ws
    | Sum ws -> sub_sum ws
    | Max ws -> smt_for_all sub ws
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  and sub_prod ws =
    match ws with
    | [] -> LB false
    | w::ws -> (sub w &^ smt_for_all eq_1_w ws) |^ (eq_1_w w &^ sub_prod ws)
  and sub_sum ws =
    match ws with
    | [] -> LB false
    | w::ws -> (sub w &^ smt_for_all eq_0_w ws) |^ (eq_0_w w &^ sub_sum ws)
  in sub

let weak_simple_on_w x =
  let rec sub w =
    match w with
    | BVar v -> LB(x = v)
    | Smt e -> LB false
    | Prod ws -> sub_prod ws
    | Sum ws -> sub_sum ws
    | Max ws -> smt_for_all sub ws
    | Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
  and sub_prod ws =
    match ws with
    | [] -> LB false
    | w::ws -> (sub w &^ smt_for_all ge_1_w ws) |^ (ge_1_w w &^ sub_prod ws)
  and sub_sum ws =
    match ws with
    | [] -> LB false
    | w::ws -> (sub w &^ smt_for_all ge_0_w ws) |^ (ge_0_w w &^ sub_sum ws)
  in sub

let vec_of_sym p solver f =
  let ty = p.base_ty in
  let to_n = int_list 1 f#arity in
  let rec sub k t =
    match t with
    | Node(WeightTemplate.Var,[]) -> Smt (solver#temp_variable ty)
    | Node(WeightTemplate.Choice,[s1;s2]) -> Cond(solver#temp_variable Bool, sub k s1, sub k s2)
    | Node(WeightTemplate.Arg i,[]) -> BVar (k,i)
    | Node(WeightTemplate.Const n,[]) -> Smt (LI n)
    | Node(WeightTemplate.Max,ss) -> Max (List.map (sub k) ss)
    | Node(WeightTemplate.Add,ss) -> Sum (List.map (sub k) ss)
    | Node(WeightTemplate.Mul,ss) -> Prod (List.map (sub k) ss)
    | Node(WeightTemplate.SumArgs,[s]) -> Sum (List.map (fun l -> sub l s) to_n)
    | Node(WeightTemplate.MaxArgs,[s]) -> Max (List.map (fun l -> sub l s) to_n)
  in
  Array.map (fun cp -> sub (-1) cp.template) p.w_params

let cw_op =
  let sub (c1,w1) (c2,ws) = match c1 &^ c2 with LB false -> None | c -> Some (c, w1 :: ws) in
  fun f cws -> List.map (fun (c,ws) -> (c, f ws)) (list_product_fold_filter sub cws [])

let distrib_cond : 'a. 'a t -> (exp * 'a t) list =
  let rec sub c w =
    if c = LB false then []
    else match w with
    | BVar _ | Smt _ -> [(c,w)]
    | Max ws -> cw_op (fun ws -> Max ws) (List.map (sub c) ws)
    | Sum ws -> cw_op (fun ws -> Sum ws) (List.map (sub c) ws)
    | Prod ws -> cw_op (fun ws -> Prod ws) (List.map (sub c) ws)
    | Cond(c1,w1,w2) -> sub (c &^ c1) w1 @ sub (c &^ smt_not c1) w2
  in fun w -> sub (LB true) w

let rec distrib_max w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Max ws -> List.concat (List.map distrib_max ws)
  | Sum ws -> List.map (fun ws -> Sum ws) (list_product (List.map distrib_max ws))
  | Prod ws -> List.map (fun ws -> Prod ws) (
      list_product_fold_filter (fun x y ->
        match x with Smt e when is_zero e -> None | _ -> Some (x::y)
      ) (List.map distrib_max ws) []
    )

let rec distrib_sum w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Sum ws -> List.concat (List.map distrib_sum ws)
  | Prod ws -> List.map (fun ws -> Prod ws) (
      list_product_fold_filter (fun x y ->
        match x with Smt e when is_zero e -> None | _ -> Some (x::y)
      ) (List.map distrib_sum ws) []
    )

(* A polynomial is represented by a map. *)
module StrIntListMap = Map.Make(LexList(Hashed (struct type t = string * int end)))

let poly_coeff vs p =
  match StrIntListMap.find_opt vs p with
  | Some e -> e
  | _ -> LI 0

let poly_add = StrIntListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let poly_sum = List.fold_left poly_add StrIntListMap.empty

let monom_mul vs1 e1 =
  let sub vs2 e2 acc = StrIntListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc in
  fun p2 -> StrIntListMap.fold sub p2 StrIntListMap.empty

let poly_mul = StrIntListMap.fold monom_mul

let poly_prod = List.fold_left poly_mul (StrIntListMap.singleton [] (LI 1))

let poly_of_w =
  let rec sub w =
    match w with
    | BVar v -> StrIntListMap.singleton [v] (LI 1)
    | Smt e -> StrIntListMap.singleton [] e
    | Sum ws -> poly_sum (List.map sub ws)
    | Prod ws -> poly_prod (List.map sub ws)
  in sub

let epoly_of_w w = List.map poly_of_w (distrib_max w)

let cepoly_of_w w = List.map (fun (c,w) -> (c, epoly_of_w w)) (distrib_cond w)

let poly_ge p1 p2 = smt_for_all (fun (vs,e2) -> poly_coeff vs p1 >=^ e2) (StrIntListMap.bindings p2)

let epoly_ge ep1 ep2 = smt_for_all (fun p2 -> smt_exists (fun p1 -> poly_ge p1 p2) ep1) ep2

let cepoly_ge cep1 cep2 =
  smt_conjunction (list_prod (fun (c1,ep1) (c2,ep2) -> (c1 &^ c2) =>^ epoly_ge ep1 ep2) cep1 cep2)

let w_ge w1 w2 = cepoly_ge (cepoly_of_w w1) (cepoly_of_w w2)

let poly_order solver p1 p2 =
  let pre = solver#refer Bool (
    smt_for_all (fun (vs,e2) -> if vs = [] then LB true else poly_coeff vs p1 >=^ e2) (StrIntListMap.bindings p2))
  in
  let e1 = poly_coeff [] p1 in
  let e2 = poly_coeff [] p2 in
  (e1 >=^ e2 &^ pre, e1 >^ e2 &^ pre)

let epoly_order solver ep1 ep2 =
  List.fold_left (fun (all_ge,all_gt) p2 ->
    let (ge,gt) =
      List.fold_left (fun (ex_ge,ex_gt) p1 ->
        let (ge,gt) = poly_order solver p1 p2 in
        (ex_ge |^ ge, ex_gt |^ gt)
      )
      (LB false, LB false)
      ep1
    in
    (all_ge &^ ge, all_gt &^ gt)
  )
  (LB true, LB true)
  ep2

let cepoly_order solver cep1 cep2 =
  let ords = list_prod_filter (fun (c1,ep1) (c2,ep2) ->
      match c1 &^ c2 with
      | LB false -> None
      | c -> let (ge,gt) = epoly_order solver ep1 ep2 in Some (c =>^ ge, c =>^ gt)
    ) cep1 cep2
  in
  let folder (ge,gt) (all_ge,all_gt) = (ge &^ all_ge, gt &^ all_gt) in
  List.fold_left folder (LB true, LB true) ords

let order_w solver w1 w2 = cepoly_order solver (cepoly_of_w w1) (cepoly_of_w w2)

let order_vec param solver =
  let dim = Array.length param.w_params in
  if dim = 0 then fun _ _ -> weakly_ordered
  else fun w1 w2 ->
    Delay (fun solver ->
      let (ge,gt) = order_w solver w1.(0) w2.(0) in
      let ge_rest = smt_for_all (fun i -> w_ge w1.(i) w2.(i)) (int_list 1 (dim-1)) in
      let ge_rest = solver#refer Bool ge_rest in
      Cons(ge &^ ge_rest, gt &^ ge_rest)
    )

let smult e = Array.map (fun w -> Prod [Smt e;w])
let add v1 v2 = Array.mapi (fun i w1 -> Sum [w1;v2.(i)]) v1

type pos_info = {
  const : exp;
  just : exp;
  weak_simple : exp;
}
type sym_info = {
  encodings : (int * int) t array;
  pos_info : pos_info array;
}

class interpreter p =
  let dim = Array.length p.w_params in
  let to_dim = int_list 0 (dim-1) in
  let put_arg =
    if dim = 0 then fun (k,_) -> puts "x_" << put_int k
    else fun (k,i) -> puts "x_" << put_int k << putc '_' << put_int i
  in
  let put_var =
    (if dim = 0 then fun (s,_) -> puts s
    else fun (s,i) -> puts s << putc '_' << put_int i)
  in
  object (x)
    val table = Hashtbl.create 64
    method init : 't. (#context as 't) -> Trs.trs -> Dp.dg -> unit = fun solver trs dg ->
      let iterer f =
        let vec = vec_of_sym p solver f in
        Hashtbl.add table f#name {
          encodings = vec;
          pos_info = Array.of_list (
            List.map (fun k ->
              {
                const = smt_for_all (fun i ->
                  smt_for_all (fun j -> const_on_w (k,i) vec.(j)) to_dim
                ) to_dim;
                just = smt_for_all (fun i -> is_var_w (k,i) vec.(i)) to_dim;
                weak_simple = smt_for_all (fun i -> weak_simple_on_w (k,i) vec.(i)) to_dim;
              }
            ) (int_list 0 (f#arity - 1))
          );
        }
      in
      trs#iter_funs iterer;
      debug (fun os ->
        os#endl; os#puts "Weight template:"; os#endl;
        trs#iter_funs (fun f ->
          x#output_sym_template f os;
          endl os
        )
      )

    method private find : 'b. (#sym as 'b) -> _ =
      fun f -> Hashtbl.find table f#name

    method constant_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) is constant *)
      fun f k -> (x#find f).pos_info.(k-1).const

    method collapses_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) = x_k *)
      fun f k -> (x#find f).pos_info.(k-1).just

    method weak_simple_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) >= x_k *)
      fun f k -> (x#find f).pos_info.(k-1).weak_simple

    method private encode_sym : 'b. (#sym as 'b) -> _ =
      fun f -> (x#find f).encodings

    method interpret : 'b. (#sym as 'b) -> (string * int) t array list -> (string * int) t array =
      fun f vs ->
      let subst = Array.of_list vs in
      let rec sub w =
        match w with
        | Smt e -> Smt e
        | BVar (k,i) -> subst.(k).(i)
        | Max ws -> Max (List.map sub ws)
        | Sum ws -> Sum (List.map sub ws)
        | Prod ws -> Prod (List.map sub ws)
        | Cond(e,w1,w2) -> Cond(e, sub w1, sub w2)
      in
      if f#is_var then Array.map (fun i -> BVar (f#name,i)) (int_array 0 (dim - 1))
      else Array.map sub (x#encode_sym f)

    method annotate : 't 'b. (#context as 't) -> (#sym as 'b) term -> ('b, (string * int) t array) wterm =
      fun solver (Node(f,ss) as t) ->
      let ts = List.map (x#annotate solver) ss in
      let vec = x#interpret f (List.map get_weight ts) in
      debug2 (endl << put_term t << puts " weight: " << put_vec put_var vec);
      WT(f, ts, refer_vec solver vec)

    method output_sym : 't 'f 'o. (#solver as 't) -> (#sym as 'f) -> (#outputter as 'o) -> unit =
      fun solver f os -> put_vec put_arg (eval_vec solver (x#encode_sym f)) os

    method output_sym_template : 'o 'f. (#sym as 'f) -> (#outputter as 'o) -> unit =
      fun f -> put_vec put_arg (x#encode_sym f)
  end


