open Sym
open Term
open Smt
open Util
open Preorder
open Params
open Io

type 'a wterm =
| BVar of 'a
| Smt of exp
| Sum of 'a wterm list
| Prod of 'a wterm list
| Max of 'a wterm list
| Cond of exp * 'a wterm * 'a wterm

let cw_op =
  let sub (c1,w1) (c2,w2) = match c1 &^ c2 with LB false -> None | c -> (c, w1 :: w2) in
  fun f ->
    let (c,ws) = list_product_filter sub in (c, f ws)

let rec distrib_cond w =
  match w with
  | BVar _ | Smt _ -> [(LB true,w)]
  | Max ws -> cw_op Max (map distrib_cond ws)
  | Sum ws -> cw_op Sum (map distrib_cond ws)
  | Prod ws -> cw_op Prod (map distrib_cond ws)
  | Cond c w1 w2 -> [(c,w1); (smt_not c, w2)]

let rec distrib_max w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Max ws -> List.concat (map distrib_max ws)
  | Sum ws -> map Sum (list_product (map distrib_max ws))
  | Prod ws -> map Prod (
      list_product_fold_filter (fun x y ->
        match x with Smt e when is_zero e -> None | _ -> Some (x::y)
      ) (map distrib_max ws)
    )

let rec distrib_sum w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Sum ws -> List.concat (map distrib_sum ws)
  | Prod ws -> map Prod (
      list_product_fold_filter (fun x y ->
        match x with Smt e when is_zero e -> None | _ -> Some (x::y)
      ) (map distrib_sum ws)
    )

(* A polynomial is represented by a map. *)

module StrListMap = Map.Make(LexList(StrHashed))

let poly_coeff vs p =
  match StrListMap.find_opt vs p with
  | Some e -> e
  | _ -> LI 0

let poly_add = StrListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let monom_mul vs1 e1 =
  let sub vs2 e2 acc = StrListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc in
  fun p2 -> StrListMap.fold sub p2 StrListMap.empty

let poly_mul = StrListMap.fold monom_mul

let rec w_to_poly w =
  match w with
  | BVar v -> StrListMap.singleton [var v] (LI 1)
  | Smt e -> StrListMap.singleton [] exp
  | Sum ws -> List.fold_left poly_add StrListMap.empty (map w_to_poly ws)
  | Prod ws -> List.fold_left poly_mul (StrListMap.singleton [] (LI 1)) (map w_to_poly ws)

let w_to_epoly w = map w_to_poly (distrib_max w)

let w_to_cepoly w = map (fun (c,w) -> (c, w_to_epoly w)) (distrib_cond w)

let poly_ge p1 p2 = smt_for_all (fun (vs,e2) -> poly_coeff vs p1 >=^ e2) (StrListMap.bindings p2)

let poly_order solver p1 p2 =
  let pre = solver#refer Bool (
    smt_for_all (fun (vs,e2) -> if vs = [] then LB true else poly_coeff vs p1 >=^ e2) (StrListMap.bindings p2))
  in
  let e1 = poly_coeff [] p1 in
  let e2 = poly_coeff [] p2 in
  (e1 >=^ e2 &^ pre, e1 >^ e2 &^ pre)

let epoly_ge ep1 ep2 = smt_for_all (fun p2 -> smt_exists (fun p1 -> poly_ge p1 p2) ep1) ep2

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

let cepoly_order solver =
  let sub = list_prod_filter (fun (c1,ep1) (c2,ep2) ->
      match c1 ^& c2 with
      | LB false -> None
      | c -> let (ge,gt) = epoly_order solver ep1 ep2 in Some (c =>^ ge, c =>^ gt)
    )
  in
  let folder (ge,gt) (all_ge,all_gt) = (ge &^ all_ge, gt &^ all_gt) in
  fun cep1 cep2 ->
  List.fold_left folder (sub cep1 cep2) (LB true, LB true)

let eval_w solver = StrListMap.map (fun es -> remdups (List.map solver#get_value es))

let put_poly p os =
  let init = ref true in
  StrListMap.iter (fun vs e ->
    if not (Smt.is_zero e) then (
      if !init then init := false else os#puts " + ";
      put_exp e os; List.iter (fun v -> os#puts "*"; os#puts v) vs
    )
  ) poly

let epoly_coeff_0 v = (* CAUSION! Non-linearity is not yet supported *)
   smt_for_all (fun p -> poly_coeff v p =^ LI 0)

let epoly_coeff_1 v = smt_for_all (fun p -> poly_coeff v p =^ LI 1)

let epoly_coeff_ge_1 v = smt_exists (fun p -> poly_coeff v p >=^ LI 1)

let eval_epoly solver ep = remdups (List.map (eval_poly solver) ep)

let put_epoly ep pr =
  match ep with
  | [] -> pr#puts "oo";
  | [p] -> put_poly p pr;
  | p::ps' -> pr#puts "max{"; put_poly p pr; List.iter (fun p' -> pr#puts ", "; put_poly p' pr;) ps'; pr#puts "}";

(* weight is array (vector) of such *)

type w_t = exp StrListMap.t list array

let order p =
  let dim = Array.length p.w_params in
  if dim = 0 then fun _ _ -> weakly_ordered
  else fun  w1 w2 ->
    Delay (fun solver ->
      let (ge,gt) = epoly_order solver w1.(0) w2.(0) in
      let ge_rest =
        (smt_for_all (fun i -> epoly_ge w1.(i) w2.(i)) (int_list 1 (dim-1)))
      in
      Cons(ge &^ ge_rest, gt)
    )

let eval_w solver = Array.map (eval_epoly solver)

let put_w w pr =
  pr#puts "[ "; Array.iter (fun ep -> put_epoly ep pr; pr#puts "; ") w; pr#puts "]"

let w_of_sym p solver f =
  let ty = p.base_ty in
  let to_n = int_list 1 f#arity in
  let rec sub k = function
    | Node(WeightTemplate.Var,[]) -> epoly_smt (solver#temp_variable ty)
    | Node(WeightTemplate.Choice(n,m),[]) -> epoly_smt (smt_if (solver#temp_variable Bool) (LI n) (LI m))
    | Node(WeightTemplate.Arg i,[]) -> epoly_bvar (k,i)
    | Node(WeightTemplate.Const n,[]) -> epoly_smt (LI n)
    | Node(WeightTemplate.Add,ss) -> epoly_sum (map (sub k) ss)
    | Node(WeightTemplate.Mul,ss) -> epoly_prod ss'
    | Node(WeightTemplate.Max,ss) -> epoly_max ss'
    | Node(WeightTemplate.SumArgs,[s]) -> epoly_sum (map (fun l -> sub l s) to_n)
    | Node(WeightTemplate.MaxArgs,[s]) -> epoly_max (map (fun l -> sub l s) to_n)
  in
  Array.map (fun cp -> sub (-1) cp.template) p.w_params

type pos_info = {
  coeff_0 : exp;
  coeff_1 : exp;
  coeff_ge_1 : exp;
}
type sym_info = {
  encodings : (int * int) wsym term array;
  no_weight : exp;
  pos_info : pos_info array;
}

class interpreter p =
  let dim = Array.length p.w_params in
  let to_dim = int_list 0 (dim-1) in
  object (x)
    val coord = (* makes suffix for coordination *)
      if dim = 0 then fun _ -> "" else fun i -> "_" ^ string_of_int i
    val coord2 =
      if dim = 0 then fun _ -> ""
      else fun i j -> "_" ^ string_of_int i ^ "_" ^ string_of_int j
    val var = fun k i -> "x_" ^ string_of_int k ^ coord i

    val table = Hashtbl.create 64

    method init : 't. (#context as 't) -> trs -> Dp.dg -> unit = fun solver trs dg ->
      let iterer f =
        let w = wexp_of_sym p solver f in
        Hashtbl.add f#name {
          encodings = w;
          no_weight = smt_for_all (fun i ->
            epoly_coeff_0 [] w.(i)
          ) to_dim;
          pos_info = Array.of_list (fun k ->
            {
              coeff_0 = smt_for_all (fun i ->
                let v = var k i in
                smt_for_all (fun j ->
                  epoly_coeff_0 v w.(j)
                ) to_dim 
              ) to_dim;
              coeff_1 = smt_for_all (fun i ->
                let v = var k i in
                smt_for_all (fun j ->
                  if i = j then epoly_coeff_1 v w.(j) else epoly_coeff_0 v w.(j)
                ) to_dim
              ) to_dim;
              coeff_ge_1 = smt_for_all (fun i ->
                let v = var k i in
                smt_for_all (fun j ->
                  if i = j then epoly_coeff_ge_1 v w.(j) else LB true
                ) to_dim
              ) to_dim;
            };
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

    method no_weight : 'b. (#sym as 'b) -> exp =
      fun f -> (x#find f).no_weight

    method constant_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) is constant *)
      fun f k -> (x#find f).pos_info.(k-1).coeff_0

    method depend_on : 'b. (#sym as 'b) -> int -> exp =
      fun f k -> smt_not (x#coeff_0 f k)

    method strict_linear_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) = x_k + ... *)
      fun f k -> (x#find f).pos_info.(k-1).coeff_1

    method weak_simple_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) >= x_k *)
      fun f k -> (x#find f).pos_info.(k-1).coeff_ge_1

    method private encode_sym : 'b. (#sym as 'b) -> _ =
      fun f -> (x#find f).encodings

    method interpret : 'b. (#sym as 'b) -> w_t list -> w_t =
      fun f ws ->
      let subst = Array.of_list ws in
      let rec sub (Node(g,ts)) =
        let ws = List.map sub ts in
        match g with
        | Smt exp    -> epoly_smt exp
        | BVar (k,i) -> subst.(k).(i)
        | Add        -> epoly_sum ws
        | Mul        -> epoly_prod ws
        | Max        -> epoly_max ws
      in
      if f#is_var then
        Array.map (fun i -> epoly_bvar (f#name ^ coord i)) (int_array 0 (dim - 1))
      else Array.map sub (x#encode_sym f)

    method annotate : 't 'b. (#context as 't) -> (#sym as 'b) term -> ('b,w_t) wterm =
      fun solver (Node(f,ss) as t) ->
      let ts = List.map (x#annotate solver) ss in
      let w = x#interpret f (List.map gpoly_weight ts) in
      let w = Array.map (List.map (StrListMap.map solver#refer_base)) w in
      debug2 (endl << put_term t << puts " weight: " << put_w w);
      WT(f,ts,w)

    method output_sym : 't 'o 'f. (#solver as 't) -> (#sym_detailed as 'f) -> (#printer as 'o) -> unit =
      fun solver f -> put_w (eval_w solver (x#encode_sym f))

    method output_sym_template : 'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
      fun f -> put_w (x#encode_sym f)
  end


