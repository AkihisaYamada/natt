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

type pos_info = {
  const : exp;
  id : exp;
}
type sym_info = {
  encodings : (int * int) wsym term array;
  pos_info : pos_info array;
}
class virtual interpreter p =
  let coord = (* makes suffix for coordination *)
    if p.w_dim = 1 then fun _ -> "" else mk_index
  in
  object (x)
    method virtual init : 't. (#context as 't) -> trs -> unit

    val table = Hashtbl.create 64

    method private find : 'b. (#sym as 'b) -> _ =
      fun f -> Hashtbl.find table f#name

    method const_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) is constant *)
      fun f k -> (x#find f).pos_info.(k-1).const

    method depend_on : 'b. (#sym as 'b) -> int -> exp =
      fun f k -> smt_not (x#const_at f k)

    method id_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) = x_k *)
      fun f k -> (x#find f).pos_info.(k-1).id

    method private encode_sym : 'b. (#sym as 'b) -> _ =
      fun f -> (x#find f).encodings

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
      else Array.map sub (x#encode_sym f)

    method annotate : 't 'b. (#context as 't) -> (#sym as 'b) term -> ('b,w_t) wterm =
      fun solver (Node(f,ss)) ->
      let ts = List.map (x#annotate solver) ss in
      let w = x#interpret f (List.map get_weight ts) in
      let w = Array.map (List.map (StrListMap.map solver#refer_base)) w in
      WT(f,ts,w)

    method output_sym :
      't 'o 'f. (#solver as 't) -> (#printer as 'o) -> string -> (#sym as 'f) -> int -> unit =
      fun solver pr prefix f n ->
      Array.iteri (fun i wexp ->
        pr#endl;
        pr#puts prefix;
        pr#puts (coord (i+1));
        pr#puts ": ";
        output_wexp solver pr wexp;
      ) (x#encode_sym f);
  end

let inner_prod xs ys = sum (List.map2 (fun x y -> prod [x;y]) xs ys)

exception Continue

let max_args trs =
  let table = Hashtbl.create 64 in
  let get f =
    try Hashtbl.find table f#name
    with Not_found -> Hashtbl.add table f#name []; []
  in
  let summarize_term test =
    let summarize_sym f =
      let max_poss = get f in
      let rec sub acc1 acc2 i = function
	| [] -> Mset.union acc1 acc2
	| vs::vss ->
	  if List.mem i max_poss then
	    sub acc1 (Mset.join acc2 vs) (i+1) vss
	  else
	    let acc1' = Mset.union acc1 vs in
	    if test acc1' then
	      sub acc1' acc2 (i+1) vss
	    else (
	      Hashtbl.replace table f#name (i :: max_poss);
	      raise Continue
	    )
      in
      sub Mset.empty Mset.empty 0
    in
    let rec sub (Node(f,ss)) =
      if f#is_var then Mset.singleton f#name
      else summarize_sym f (List.map sub ss)
    in
    sub
  in
  let rec loop () =
    try
      trs#iter_rules (fun i rule ->
        let lvs = summarize_term (fun _ -> true) rule#l in
        ignore (summarize_term (Mset.supseteq lvs) rule#r)
      )
    with Continue -> loop ()
  in
  loop ();
  table
;;

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
        let max_arg =
          match p.max_mode with
          | MAX_dup ->
            let t = max_args trs in
            fun f i -> IntSet.mem (Hashtbl.find f#name t) i
          | MAX_all ->
            fun _ _ -> true
          | MAX_none ->
            fun _ _ -> false
        in
        trs#iter_funs (fun f ->
          let w = "w_" ^ f#name in
          let c = "c_" ^ f#name in
          for i = 1 to p.w_dim do
              let w_i = w ^ coord i in
              add_number p.w_mode solver w;
              solver#add_assertion (ref_weight w >=^ LI 0);
              for k = 1 to f#arity do
                let c_ki = c ^ mk_index k ^ coord i in
                for j = 1 to p.w_dim do
                  let c_kij = c_ki ^ coord j in
                  add_number p.sc_mode solver c_kij;
                  bind_upper solver (ref_coeff c_kij);
                  if not p.dp && i = 1 then begin
                    solver#add_assertion (ref_coeff c_kij >=^ LI 1);
                  end
                done
              done
            done;
            Hashtbl.add table f#name {
              encodings = Array.map (
                fun i -> sum (
                    smt (ref_weight (w ^ coord i)) ::
                    List.map (fun k ->
                      inner_prod (coeff_row (c ^ mk_index k ^ coord i)) (bvar_vec (k-1))
                    ) (int_list 1 f#arity)
                  )
                ) (int_array 1 p.w_dim);
              pos_info = Array.map (
                fun k -> {
                  const = solver#refer Bool (
                    smt_for_all
                      (fun i -> ref_coeff (c ^ mk_index k ^ coord i) =^ LI 0)
                      (int_list 1 p.w_dim)
                    );
                  id = smt_for_all (
                    fun i ->
                      (ref_coeff (c ^ mk_index k ^ coord i) =^ LI 1) &^
                      (ref_weight (w ^ coord i) =^ LI 0)
                    ) (int_list 1 p.w_dim);
                }
              ) (int_array 1 f#arity);
            }
          )
  end


