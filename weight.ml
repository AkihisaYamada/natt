open Sym
open Term
open Smt
open Util
open Preorder
open Params
open Io

type 'a wsym = Smt of exp | Add | Mul | Max | BVar of 'a

let wexp_bvar name = Node(BVar name, [])
let wexp_smt exp = Node(Smt exp, [])

let wexp_sum ss =
  match List.filter ((<>) (wexp_smt (LI 0))) ss with
  | [] -> wexp_smt (LI 0)
  | [s] -> s
  | ss' -> Node(Add, ss')

let wexp_prod ss =
  if List.exists ((=) (wexp_smt (LI 0))) ss then
    wexp_smt (LI 0)
  else
    match List.filter ((<>) (wexp_smt (LI 1))) ss with
    | [] -> wexp_smt (LI 1)
    | [s] -> s
    | ss' -> Node(Mul, ss')

let wexp_max ss =
  match remdups ss with
  | [] -> wexp_smt (LI 0)
  | [s] -> s
  | ss' -> Node(Max, ss')

let put_wexp var e (os : #printer) =
  let rec sub lvl =
    function
    | Node(Smt exp,[]) -> put_exp exp os
    | Node(Add, es) ->
      if es = [] then os#puts "0"
      else begin
        if lvl > 1 then os#puts "(";
        punct_list (sub 1) (puts " + ") es os;
        if lvl > 1 then os#puts ")"
      end
    | Node(Mul, es) ->
      if es = [] then os#puts "1"
      else punct_list (sub 2) (puts " * ") es os
    | Node(Max, es) ->
      os#puts "max {"; punct_list (sub 0) (puts ", ") es os; os#puts "}";
    | Node(BVar v, []) -> var v os
  in
  sub 0 e

let eval_wexp solver =
  let rec sub (Node(f,ss)) =
    let ss = List.map sub ss in
    match f with
    | Smt exp -> wexp_smt (solver#gpoly_value exp)
    | Add -> wexp_sum ss
    | Mul -> wexp_prod ss
    | Max -> wexp_max ss
    | _ -> Node(f,ss)
  in
  sub

let wexp_map_var var =
  let rec sub (Node(f,ss)) =
    match f with
    | BVar v -> wexp_bvar (var v)
    | _ -> Node(f, List.map sub ss)
  in sub

(* Polynomial as a map from var list to coefficients *)

module StrListMap = Map.Make(LexList(StrHashed))

let poly_smt exp = StrListMap.singleton [] exp

let poly_bvar name = StrListMap.singleton [name] (LI 1)

let poly_find vs et =
  try StrListMap.find vs et with Not_found -> LI 0

let poly_add = StrListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let poly_sum = List.fold_left poly_add StrListMap.empty

let poly_mul_one vs1 e1 et2 =
  StrListMap.fold
    (fun vs2 e2 acc -> StrListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc)
    et2
    StrListMap.empty

let poly_mul wt1 wt2 =
   StrListMap.fold poly_mul_one wt1 wt2

let poly_prod = List.fold_left poly_mul StrListMap.empty

let poly_ge et1 et2 =
  smt_for_all (fun (vs,e2) -> poly_find vs et1 >=^ e2) (StrListMap.bindings et2)

let poly_order solver et1 et2 =
  let pre = (* tests >= for all coefficients but the constant part *)
    smt_for_all
        (fun (vs,e2) -> if vs = [] then LB true else poly_find vs et1 >=^ e2)
        (StrListMap.bindings et2)
  in
  let pre = solver#refer Bool pre in
  let e1 = poly_find [] et1 in
  let e2 = poly_find [] et2 in
  (pre &^ (e1 >=^ e2), pre &^ (e1 >^ e2))

let poly_coeff v et = (* CAUSION! Non-linearity is not yet supported *)
  match StrListMap.find_opt v et with
  | Some e -> e
  | _ -> LI 0

let put_poly poly pr =
  let init = ref true in
  StrListMap.iter (fun vs e ->
    if !init then init := false else pr#puts " + ";
    put_exp e pr; List.iter (fun v -> pr#puts "*"; pr#puts v) vs
  ) poly


(* Max are expanded as lists *)

let epoly_smt exp = [poly_smt exp]

let epoly_bvar name = [poly_bvar name]

let epoly_sum etss =
  List.map poly_sum (list_product etss)

let epoly_prod etss = List.map poly_prod (list_product etss)

let epoly_max = List.concat

let epoly_ge ep1 ep2 =
  smt_for_all (fun p2 -> smt_exists (fun p1 -> poly_ge p1 p2) ep1) ep2

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

let epoly_coeff_0 v = smt_for_all (fun p -> poly_coeff v p =^ LI 0)

let epoly_coeff_1 v = smt_for_all (fun p -> poly_coeff v p =^ LI 1)

let epoly_coeff_ge_1 v = smt_exists (fun p -> poly_coeff v p >=^ LI 1)

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

let put_w w pr =
  pr#puts "[ "; Array.map (fun ep -> put_epoly ep pr; pr#puts "; ") w; pr#puts "]"

let w_of_sym p solver f =
  let ty = p.base_ty in
  let to_n = int_list 1 f#arity in
  let rec sub k = function
    | Node(WeightTemplate.Var,[]) -> wexp_smt (solver#temp_variable ty)
    | Node(WeightTemplate.Choice,[s1;s2]) -> wexp_smt (smt_if (solver#temp_variable Bool) (sub k s1) (sub k s2))
    | Node(Arg i,[]) -> wexp_bvar (k,i)
    | Node(Const n,[]) -> wexp_smt (LI n)
    | Node(WeightTemplate.Add,ss) -> wexp_sum (map (sub k) ss)
    | Node(WeightTemplate.Mul,ss) -> wexp_prod ss'
    | Node(WeightTemplate.Max,ss) -> wexp_max ss'
    | Node(WeightTemplate.SumArgs,[s]) -> wexp_sum (map (fun l -> sub l s) to_n)
    | Node(WeightTemplate.MaxArgs,[s]) -> wexp_max (map (fun l -> sub l s) to_n)
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
      fun solver f ->
      puts "[" << (fun pr ->
        let punct = ref "" in
        Array.iteri (fun i wexp ->
          pr#puts !punct;
          (put_wexp put_var (eval_wexp solver wexp)) pr;
          punct := ", "
        ) (x#encode_sym f);
      ) <<
      puts "]"

    method output_sym_template : 'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
      fun f pr ->
      pr#puts "  ";
      f#output pr;
      pr#puts ":\t[";
      let punct = ref " " in
      Array.iteri (fun i wexp ->
        pr#puts !punct;
        punct := ",\n\t  ";
        put_wexp put_var wexp pr;
      ) (x#encode_sym f);
      pr#puts " ]"
  end


