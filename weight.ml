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

let zero_w = Smt (LI 0)
let one_w = Smt (LI 1)

let sum ws =
   match List.filter (fun w -> w <> zero_w) ws with
   | [] -> zero_w
   | [w] -> w
   | ws -> Sum ws

let prod ws =
  if List.exists (fun w -> w = zero_w) ws then zero_w else
  match List.filter (fun w -> w <> one_w) ws with
  | [] -> one_w
  | [w] -> w
  | ws -> Prod ws

let eval_w solver =
  let rec sub w =
    match w with
    | BVar _ -> w
    | Smt e -> Smt (solver#get_value e)
    | Prod ws -> prod (List.map sub ws)
    | Sum ws -> sum (List.map sub ws)
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
    | BVar v -> LB (x <> v)
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
    | Max ws -> smt_exists sub ws
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

let put_w var : 'a t -> #printer -> unit =
  let paren l l' m = if l <= l' then m else putc '(' << m << putc ')' in
  let rec sub l w =
    match w with
    | BVar v -> var v
    | Smt e -> put_exp e
    | Prod ws ->
      if List.exists (fun w -> w = Smt (LI 0)) ws then putc '0'
      else
       let ws = List.filter (fun w -> w <> Smt (LI 1)) ws in 
       paren l 2 (put_list (sub 2) (puts " * ") (putc '1') ws)
    | Sum ws ->
      let ws = List.filter (fun w -> w <> Smt (LI 0)) ws in
      paren l 1 (put_list (sub 1) (puts " + ") (putc '0') ws)
    | Max ws -> puts "max{" << put_list (sub 0) (puts ", ") (puts "-oo") ws << puts "}"
    | Cond(e,w1,w2) -> paren l 0 (put_exp e << puts " ? " << sub 1 w1 << puts " : " << sub 0 w2)
  in
  fun w os -> (sub 0 w) os

let put_vec var wa = puts "(" << put_list (put_w var) (puts ", ") (puts "-") (Array.to_list wa) << puts ")"

let cw_op =
  let sub (c1,w1) (c2,ws) = match c1 &^ c2 with LB false -> None | c -> Some (c, w1 :: ws) in
  fun f cws -> List.map (fun (c,ws) -> (c, f ws)) (list_product_fold_filter sub cws [(LB true,[])])

let expand_cond : 'a. 'a t -> (exp * 'a t) list =
  let rec sub c w =
    if c = LB false then []
    else match w with
    | BVar _ | Smt _ -> [(c,w)]
    | Max ws -> cw_op (fun ws -> Max ws) (List.map (sub c) ws)
    | Sum ws -> cw_op (fun ws -> sum ws) (List.map (sub c) ws)
    | Prod ws -> cw_op (fun ws -> prod ws) (List.map (sub c) ws)
    | Cond(c1,w1,w2) -> sub (c &^ c1) w1 @ sub (c &^ smt_not c1) w2
  in fun w -> sub (LB true) w

let put_cws var cws =
  puts "{ " <<
  put_list (fun (c,w) -> put_exp c << puts "\t:--> " << put_w var w) (puts "\n  ") (puts "??") cws <<
  puts "}"

let rec expand_max w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Max ws -> List.concat (List.map expand_max ws)
  | Sum ws -> List.map (fun ws -> sum ws) (list_product (List.map expand_max ws))
  | Prod ws -> List.map (fun ws -> prod ws) (list_product (List.map expand_max ws))

let rec expand_sum w =
  match w with
  | BVar _ | Smt _ -> [w]
  | Sum ws -> List.concat (List.map expand_sum ws)
  | Prod ws -> List.map (fun ws -> prod ws) (
      list_product_fold_filter (fun x y ->
        match x with Smt e when is_zero e -> None | _ -> Some (x::y)
      ) (List.map expand_sum ws) []
    )

(* A polynomial is represented by a map. *)
module StrIntListMap = Map.Make(LexList(Hashed (struct type t = string * int end)))

let put_var (v,i) = putc '<' << puts v << putc '_' << put_int (i+1) << putc '>'

let poly_coeff vs p =
  match StrIntListMap.find_opt vs p with
  | Some e -> e
  | _ -> LI 0

let put_poly p os =
  StrIntListMap.iter (fun vs e -> os#puts " + "; put_exp e os; List.iter (fun v -> puts "*" os; put_var v os) vs) p

let put_epoly ep = puts "max {" << put_list put_poly (puts ", ") nop ep << puts "}"

let add_poly = StrIntListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let sum_poly = List.fold_left add_poly StrIntListMap.empty

let mul_monom vs1 e1 =
  let sub vs2 e2 acc = StrIntListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc in
  fun p2 -> StrIntListMap.fold sub p2 StrIntListMap.empty

let mul_poly = StrIntListMap.fold mul_monom

let prod_poly = List.fold_left mul_poly (StrIntListMap.singleton [] (LI 1))

let poly_of_w =
  let rec sub w =
    match w with
    | BVar v -> StrIntListMap.singleton [v] (LI 1)
    | Smt e -> StrIntListMap.singleton [] e
    | Sum ws -> sum_poly (List.map sub ws)
    | Prod ws -> prod_poly (List.map sub ws)
  in sub

let ge_poly p1 p2 = smt_for_all (fun (vs,e2) -> poly_coeff vs p1 >=^ e2) (StrIntListMap.bindings p2)

let ge_max w1 w2 =
  let ew1 = expand_max w1 in
  let ew2 = expand_max w2 in
  let ep1 = List.map poly_of_w ew1 in
  let ep2 = List.map poly_of_w ew2 in
  smt_for_all (fun p2 -> smt_exists (fun p1 -> ge_poly p1 p2) ep1) ep2

let ge_w w1 w2 =
  let cws1 = expand_cond w1 in
  let cws2 = expand_cond w2 in
  smt_conjunction (list_prod (fun(c1,w1) (c2,w2) -> (c1 &^ c2) =>^ ge_max w1 w2) cws1 cws2)

let order_poly solver p1 p2 =
  let pre = solver#refer Bool (
    smt_for_all (fun (vs,e2) -> if vs = [] then LB true else poly_coeff vs p1 >=^ e2) (StrIntListMap.bindings p2))
  in
  let e1 = poly_coeff [] p1 in
  let e2 = poly_coeff [] p2 in
  let ge = (e1 >=^ e2) &^ pre in
  let gt = (e1 >^ e2) &^ pre in
  debug2 (
    endl << puts "[order_poly] "  << put_poly p1 << puts " vs. " << put_poly p2 <<
    endl << puts "[order_poly] ge: " << put_exp ge <<
    endl << puts "[order_poly] gt: " << put_exp gt);
  (ge, gt)

let order_max solver w1 w2 =
  let ew1 = expand_max w1 in
  let ew2 = expand_max w2 in
  let ep1 = List.map poly_of_w ew1 in
  let ep2 = List.map poly_of_w ew2 in
  debug2(endl << puts "[order_max] " << put_w put_var w1 << puts " vs. " << put_w put_var w2);
  let (ge,gt) =
    List.fold_left (fun (all_ge,all_gt) p2 ->
      let (ge,gt) =
        List.fold_left (fun (ex_ge,ex_gt) p1 ->
          let (ge,gt) = order_poly solver p1 p2 in
          (ex_ge |^ ge, ex_gt |^ gt)
        )
        (LB false, LB false)
        ep1
      in
      (all_ge &^ ge, all_gt &^ gt)
    )
    (LB true, LB true)
    ep2
  in
  (ge,gt)

let order_w solver w1 w2 =
  let cws1 = expand_cond w1 in
  let cws2 = expand_cond w2 in
  debug2(endl << puts "[order_w] " << put_w put_var w1 << puts " vs. " << put_w put_var w2);
  let ords = list_prod_filter (fun (c1,w1) (c2,w2) ->
      match c1 &^ c2 with
      | LB false -> None
      | c ->
        let (ge,gt) = order_max solver w1 w2 in Some (c =>^ ge, c =>^ gt)
    ) cws1 cws2
  in
  let folder (ge,gt) (all_ge,all_gt) = (ge &^ all_ge, gt &^ all_gt) in
  let (ge,gt) = List.fold_left folder (LB true, LB true) ords in
  (ge,gt)

let order_vec param solver =
  let dim = Array.length param.w_templates in
  if dim = 0 then fun _ _ -> weakly_ordered
  else fun w1 w2 ->
    Delay (fun solver ->
      let (ge,gt) = order_w solver w1.(0) w2.(0) in
      let ge_rest = smt_for_all (fun i -> ge_w w1.(i) w2.(i)) (int_list 1 (dim-1)) in
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
  let dim = Array.length p.w_templates in
  let to_dim = int_list 0 (dim-1) in
  let put_arg =
    if dim = 1 then fun (k,_) -> puts "x" << put_int (k+1)
    else fun (k,i) -> puts "x" << put_int (k+1) << putc '_' << put_int (i+1)
  in
  let ty = p.base_ty in
  object (x)
    val table = Hashtbl.create 64
    method init : 't. (#context as 't) -> Trs.trs -> Dp.dg -> unit = fun solver trs dg ->
      let iterer f =
        let n = f#arity in
        let to_n = int_list 0 (n-1) in
        let rec sub k t =
            match t with
            | WeightTemplate.PosVar ->
              let v = solver#temp_variable ty in
              solver#add_assertion (v >=^ LI 0);
              Smt v
            | WeightTemplate.NegVar ->
              let v = solver#temp_variable ty in
              Smt v
            | WeightTemplate.Choice [t1;t2] ->
              let w1 = sub k t1 in
              let w2 = sub k t2 in
              let c = solver#temp_variable Bool in
              ( match w1, w2 with
                | BVar v, Smt (LI 0) -> Prod [Smt(smt_if c (LI 1) (LI 0)); BVar v]
                | Smt (LI 0), BVar v -> Prod [Smt(smt_if c (LI 0) (LI 1)); BVar v]
                | Smt e1, Smt e2 -> Smt(smt_if c e1 e2)
                | _ -> Cond(c,w1,w2)
              )
            | WeightTemplate.Arg i -> BVar (k,i)
            | WeightTemplate.Const n -> Smt (LI n)
            | WeightTemplate.Prod ts -> Prod (List.map (sub k) ts)
            | WeightTemplate.Sum ts -> Sum (List.map (sub k) ts)
            | WeightTemplate.Max ts -> Max (List.map (sub k) ts)
            | WeightTemplate.SumArgs t -> Sum (List.map (fun l -> sub l t) to_n)
            | WeightTemplate.MaxArgs t -> Max (List.map (fun l -> sub l t) to_n)
            | WeightTemplate.Arity0(t1,t2) -> sub k (if n = 0 then t1 else t2)
            | WeightTemplate.Arity1(t1,t2) -> sub k (if n = 1 then t1 else t2)
        in
        let vec = Array.map (fun t -> sub (-1) t) p.w_templates in
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

    method private find : 'f. (#sym as 'f) -> _ =
      fun f -> Hashtbl.find table f#name

    method constant_at : 'f. (#sym as 'f) -> int -> exp =
      (* <--> [f](..x_k..) is constant *)
      fun f k -> (x#find f).pos_info.(k-1).const

    method collapses_at : 'f. (#sym as 'f) -> int -> exp =
      (* <--> [f](..x_k..) = x_k *)
      fun f k -> (x#find f).pos_info.(k-1).just

    method weak_simple_at : 'f. (#sym as 'f) -> int -> exp =
      (* <--> [f](..x_k..) >= x_k *)
      fun f k -> (x#find f).pos_info.(k-1).weak_simple

    method private encode_sym : 'f. (#sym as 'f) -> _ =
      fun f -> (x#find f).encodings

    method interpret : 'f. (#sym as 'f) -> (string * int) t array list -> (string * int) t array =
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

    method annotate : 't 'f. (#context as 't) -> (#sym as 'f) term -> ('f, (string * int) t array) wterm =
      fun solver (Node(f,ss) as t) ->
      let ts = List.map (x#annotate solver) ss in
      let vec = x#interpret f (List.map get_weight ts) in
      WT(f, ts, refer_vec solver vec)

    method output_sym : 't 'f 'o. (#solver as 't) -> (#Trs.sym_detailed as 'f) -> (#printer as 'o) -> unit =
      fun solver f os -> put_vec put_arg (eval_vec solver (x#encode_sym f)) os;
         os#puts "\tinfo: ";
           for i = 1 to f#arity do
             os#putc ' ';
             if solver#get_bool (x#constant_at f i)  then os#putc '0';
             if solver#get_bool (x#collapses_at f i) then os#putc '1';
             if solver#get_bool (x#weak_simple_at f i) then os#putc 's';
           done

    method output_sym_template : 'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
      fun f -> f#output << puts ": " << put_vec put_arg (x#encode_sym f)
  end



