open Sym
open Term
open Trs
open Smt
open Util
open Preorder
open Params
open Io

module StrListMap = Map.Make(LexList(StrHashed));;

type 'a wsym = Smt of exp | Add | Mul | Max | BVar of 'a

let bvar name = Node(BVar name, [])
let smt exp = Node(Smt exp, [])
let sum ss = Node(Add,ss)
let prod ss = Node(Mul,ss)
let max ss = Node(Max,ss)

let rec output_wexp (solver : #solver) (os : #printer) e =
  match e with
  | Node(Smt exp,[]) -> output_exp os (solver#get_value exp)
  | Node(Add, e::es) ->
    output_wexp solver os e;
    List.iter (fun e -> os#puts " + "; output_wexp solver os e) es
  | Node(Mul, e::es) ->
    output_wexp solver os e;
    List.iter (fun e -> os#puts " * "; output_wexp solver os e) es
  | Node(Max, e::es) ->
    output_wexp solver os e;
    os#puts "max {";
    List.iter (fun e -> os#puts ", "; output_wexp solver os e) es;
    os#puts "}";
  | Node(BVar (k,i), []) ->
    os#puts "x";
    os#put_int (k+1);
    os#puts "_";
    os#put_int (i+1)
;;

(* Weight as a map from var list to exp *)

let wt_find vs wt =
  try StrListMap.find vs wt with Not_found -> LI 0

let wt_add = StrListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let wt_sum = List.fold_left wt_add StrListMap.empty

let wt_mul_one vs1 e1 wt2 =
  StrListMap.fold
    (fun vs2 e2 acc -> StrListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc)
    wt2
    StrListMap.empty

let wt_mul wt1 wt2 =
   StrListMap.fold wt_mul_one wt1 wt2

let wt_prod = List.fold_left wt_mul StrListMap.empty

let order =
  let ge_wt wt1 wt2 =
    smt_for_all (fun (vs,e) -> wt_find vs wt1 >=^ e) (StrListMap.bindings wt2)
  in
  let order_wt solver wt1 wt2 =
    let ge = solver#refer Bool (ge_wt wt1 wt2) in
    (ge, ge &^ (wt_find [] wt1 >^ wt_find [] wt2))
  in
  let ge_wts wts1 wts2 =
    smt_for_all (fun wt2 -> smt_exists (fun wt1 -> ge_wt wt1 wt2) wts1) wts2
  in
  let order_wts solver wts1 wts2 =
    List.fold_left (fun (all_ge,all_gt) wt2 ->
      let (ge,gt) =
        List.fold_left (fun (ex_ge,ex_gt) wt1 ->
          let (ge,gt) = order_wt solver wt1 wt2 in
          (ex_ge |^ ge, ex_gt |^ gt)
        )
        (LB false, LB false)
        wts1
      in
      (all_ge &^ ge, all_gt &^ gt)
    )
    (LB true, LB true)
    wts2
  in
  fun solver dim wtsa1 wtsa2 ->
    let (ge,gt) = order_wts solver wtsa1.(0) wtsa2.(0) in
    let ge_rest = solver#refer Bool
      (smt_for_all (fun i -> ge_wts wtsa1.(i) wtsa2.(i)) (int_list 1 (dim-1)))
    in
    Cons(ge &^ ge_rest, gt &^ ge_rest)

let mk_index i = "_" ^ string_of_int i

let wt_bvar name = StrListMap.singleton [name] (LI 1)

type w_t = exp StrListMap.t list array

let make_tri a b =
  smt_if a (smt_if b (LI 2) (LI 1)) (LI 0)

let make_quad a b =
  smt_if a (smt_if b (LI 3) (LI 2)) (smt_if b (LI 1) (LI 0))

let ref_number w_mode =
  match w_mode with
  | W_num -> fun v -> EV v
  | W_bool -> fun v -> PB (EV v)
  | W_tri -> fun v -> make_tri (EV (v ^ "-a")) (EV (v ^ "-b"))
  | W_quad -> fun v -> make_quad (EV (v ^ "-a")) (EV (v ^ "-b"))
  | W_none -> fun _ -> LI 0

let add_number : _ -> #context -> _ =
  function
  | W_num -> fun solver v -> solver#add_variable_base v
  | W_bool -> fun solver v -> solver#add_variable v Bool
  | W_tri -> fun solver v ->
    solver#add_variable (v ^ "-a") Bool;
    solver#add_variable (v ^ "-b") Bool
  | W_quad -> fun solver v ->
    solver#add_variable (v ^ "-a") Bool;
    solver#add_variable (v ^ "-b") Bool
  | W_none -> fun _ _ -> ()

class virtual interpreter p =
  let coord = (* makes suffix for coordination *)
    if p.w_dim = 1 then fun _ -> "" else mk_index
  in
  object (x)
    method virtual init : 't. (#context as 't) -> trs -> unit
    method virtual private encode_sym : 'b. (#sym as 'b) -> int -> (int * int) wsym term array
    method interpret : 'b. (#sym as 'b) -> w_t list -> w_t =
      fun f wtsas ->
      let subst = Array.of_list wtsas in
      let rec sub (Node(g,ts)) =
        let wtss = List.map sub ts in
        match g with
        | Smt exp    -> [StrListMap.singleton [] exp]
        | BVar (k,i) -> subst.(k).(i)
        | Add        -> List.map wt_sum (list_product wtss)
        | Mul        -> List.map wt_prod (list_product wtss)
        | Max        -> List.concat wtss
      in
      if f#is_var then
        Array.map (fun i -> [wt_bvar (f#name ^ coord i)]) (int_array 0 (p.w_dim - 1))
      else Array.map sub (x#encode_sym f (List.length wtsas))

    method annotate : 't 'b. (#context as 't) -> (#sym as 'b) term -> ('b,w_t) wterm =
      fun solver (Node(f,ss)) ->
        let ts = List.map (x#annotate solver) ss in
        let w = x#interpret f (List.map get_weight ts) in
        let w = Array.map (List.map (StrListMap.map solver#refer_base)) w in
        WT(f,ts,w)

    method output_sym :
      't 'o 'f. (#solver as 't) -> (#printer as 'o) -> (#sym as 'f) -> int -> unit
    = fun solver pr f n ->
        Array.iteri (fun i wexp ->
          pr#endl;
          pr#puts "\t";
          pr#put_int (i+1);
          pr#puts ": ";
          output_wexp solver pr wexp;
        ) (x#encode_sym f n);
  end

let inner_prod xs ys = sum (List.map2 (fun x y -> prod [x;y]) xs ys)

class pol_interpreter p =
  let coord = (* makes suffix for coordination *)
    if p.w_dim = 1 then fun _ -> "" else mk_index
  in
  let ref_weight = ref_number p.w_mode in
  let ref_coeff = ref_number p.sc_mode in
  let coeff_row name =
    List.map (fun j -> smt (ref_coeff (name ^ coord j))) (int_list 1 p.w_dim)
  in
  let bvar_vec k = List.map (fun i -> bvar (k,i)) (int_list 0 (p.w_dim - 1)) in
  let bind_upper =
    if p.w_max = 0 then fun _ _ -> ()
    else fun solver fw -> solver#add_assertion (fw <=^ LI p.w_max)
  in
  object (x)
    inherit interpreter p
    method init : 't. (#context as 't) -> trs -> unit =
      fun solver trs ->
        trs#iter_syms (fun f ->
          if f#is_fun then
            for i = 1 to p.w_dim do
              let w = ("w_" ^ f#name ^ coord i) in
              add_number p.w_mode solver w;
              solver#add_assertion (ref_weight w >=^ LI 0);
              for k = 1 to f#arity do
                for j = 1 to p.w_dim do
                  let c = "c_" ^ f#name ^ mk_index k ^ coord i ^ coord j in
                  add_number p.sc_mode solver c;
                  bind_upper solver (ref_coeff c);
                  if not p.dp && i = 1 then begin
                    solver#add_assertion (ref_coeff c >=^ LI 1);
                  end
                done
              done
            done
        )
    method private encode_sym : 'b. (#sym as 'b) -> _ =
      fun f n ->
        Array.map (fun i ->
          sum (
            smt (ref_weight ("w_" ^ f#name ^ coord i)) ::
            List.map (fun k ->
              inner_prod (coeff_row ("c_" ^ f#name ^ mk_index k ^ coord i)) (bvar_vec (k-1))
            ) (int_list 1 n)
          )
        ) (int_array 1 p.w_dim)
  end


