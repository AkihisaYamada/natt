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

let punct_list elem punc (os : #printer) =
  let rec sub = function
    | [] -> ()
    | x::xs -> punc os; elem x; sub xs
  in
  function
  | [] -> ()
  | x::xs -> elem x; sub xs

let put_wexp_inner smt e (os : #printer) =
  let rec sub =
    function
    | Node(Smt exp,[]) -> smt exp os
    | Node(Add, es) -> punct_list sub (puts " + ") os es
    | Node(Mul, es) -> punct_list sub (puts " * ") os es
    | Node(Max, es) -> os#puts "max {"; punct_list sub (puts ", ") os es; os#puts "}";
    | Node(BVar (k,i), []) ->
      os#puts "x";
      os#put_int (k+1);
      os#puts "_";
      os#put_int (i+1)
  in
  sub e

let put_wexp e os = put_wexp_inner put_exp e os

let eval_wexp solver = put_wexp_inner (fun exp -> put_exp (solver#get_value exp))

(* Weight as a map from var list to exp *)

let et_smt exp = StrListMap.singleton [] exp

let et_bvar name = StrListMap.singleton [name] (LI 1)

let et_find vs et =
  try StrListMap.find vs et with Not_found -> LI 0

let et_add = StrListMap.union (fun vs e1 e2 -> Some (e1 +^ e2))

let et_sum = List.fold_left et_add StrListMap.empty

let et_mul_one vs1 e1 et2 =
  StrListMap.fold
    (fun vs2 e2 acc -> StrListMap.add (List.merge compare vs1 vs2) (e1 *^ e2) acc)
    et2
    StrListMap.empty

let et_mul wt1 wt2 =
   StrListMap.fold et_mul_one wt1 wt2

let et_prod = List.fold_left et_mul StrListMap.empty

let et_ge et1 et2 =
  smt_for_all (fun (vs,e) -> et_find vs et1 >=^ e) (StrListMap.bindings et2)

let et_order solver et1 et2 =
  let ge = solver#refer Bool (et_ge et1 et2) in
  (ge, ge &^ (et_find [] et1 >^ et_find [] et2))

(* Max are expanded as lists *)

let ets_smt exp = [et_smt exp]

let ets_bvar name = [et_bvar name]

let ets_sum etss =
debug2 (puts "entering ets_sum: " << flush);
debug2 (put_int (List.length (list_product etss)) << endl);
let ret =  List.map et_sum (list_product etss)
in
debug2 (puts "leaving" << endl);
ret

let ets_prod etss = List.map et_prod (list_product etss)

let ets_max = List.concat

let ets_ge ets1 ets2 =
  smt_for_all (fun et2 -> smt_exists (fun et1 -> et_ge et1 et2) ets1) ets2

let ets_order solver ets1 ets2 =
  List.fold_left (fun (all_ge,all_gt) et2 ->
    let (ge,gt) =
      List.fold_left (fun (ex_ge,ex_gt) et1 ->
        let (ge,gt) = et_order solver et1 et2 in
        (ex_ge |^ ge, ex_gt |^ gt)
      )
      (LB false, LB false)
      ets1
    in
    (all_ge &^ ge, all_gt &^ gt)
  )
  (LB true, LB true)
  ets2

(* weight is array (vector) of such *)

let add = Array.map2 (fun ets1 ets2 -> ets_sum [ets1;ets2])

let smult exp = Array.map (List.map (et_mul_one [] exp))

let order dim w1 w2 =
  Delay (fun solver ->
    let (ge,gt) = ets_order solver w1.(0) w2.(0) in
    let ge_rest = solver#refer Bool
      (smt_for_all (fun i -> ets_ge w1.(i) w2.(i)) (int_list 1 (dim-1)))
    in
    Cons(ge &^ ge_rest, gt &^ ge_rest)
  )

let index i = "_" ^ string_of_int i

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
  weak_simple : exp;
}
type sym_info = {
  encodings : (int * int) wsym term array;
  pos_info : pos_info array;
}
class virtual interpreter p =
  let coord = (* makes suffix for coordination *)
    if p.w_dim = 1 then fun _ -> "" else index
  in
  object (x)
    method virtual init : 't. (#context as 't) -> trs -> Dp.dg -> unit

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

    method weak_simple_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) >= x_k *)
      fun f k -> (x#find f).pos_info.(k-1).weak_simple

    method private encode_sym : 'b. (#sym as 'b) -> _ =
      fun f -> (x#find f).encodings

    method interpret : 'b. (#sym as 'b) -> w_t list -> w_t =
      fun f ws ->
      let subst = Array.of_list ws in
      let rec sub (Node(g,ts)) =
        let ws = List.map sub ts in
        match g with
        | Smt exp    -> ets_smt exp
        | BVar (k,i) -> subst.(k).(i)
        | Add        -> ets_sum ws
        | Mul        -> ets_prod ws
        | Max        -> ets_max ws
      in
      if f#is_var then
        Array.map (fun i -> ets_bvar (f#name ^ coord i)) (int_array 0 (p.w_dim - 1))
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
        (endl << puts prefix << puts (coord (i+1)) << puts ": " << eval_wexp solver wexp) pr
      ) (x#encode_sym f);
  end

exception Continue

class enc_pos_info s m = object
  val mutable in_sum : bool = s
  val mutable in_max : bool = m
  method set_sum b = in_sum <- b
  method set_max b = in_max <- b
  method in_sum = in_sum
  method in_max = in_max
end


let maxpoly_heuristic (trs:trs) (dg:Dp.dg) either =
object (x)

  val table = Hashtbl.create 64

  method private get : 'f. (#sym as 'f) -> _ =
  fun f ->
    try Hashtbl.find table f#name
    with Not_found ->
      let ret =
        (Array.init (trs#find_sym f)#arity (fun k -> new enc_pos_info true false))
      in
      Hashtbl.add table f#name ret;
      ret

  method info f k = (x#get f).(k)

  initializer
    let summarize_term test =
      let summarize_sym f =
        let arr = x#get f in
        let rec sub acc i = function
	  | [] -> acc
	  | vs::vss ->
	    if arr.(i)#in_max then
	      sub (Mset.join acc vs) (i+1) vss
	    else
	      let acc' = Mset.union acc vs in
	      if test acc' then
	        sub acc' (i+1) vss
	      else (
	        arr.(i)#set_max true;
	        if either then arr.(i)#set_sum false;
	        raise Continue
	      )
        in
        sub Mset.empty 0
      in
      let rec sub (Node(f,ss)) =
        if f#is_var then Mset.singleton f#name
        else summarize_sym f (List.map sub ss)
      in
      sub
    in
    let rec loop () =
      try
        dg#iter_dps (fun i rule ->
          let lvs = summarize_term (fun _ -> true) rule#l in
          ignore (summarize_term (Mset.supseteq lvs) rule#r)
        )
      with Continue -> loop ()
    in
    loop ()
end;;

class pol_interpreter p =
  let coord = (* makes suffix for coordination *)
    if p.w_dim = 1 then fun _ -> "" else index
  in
  let ref_weight = ref_number p.w_mode in
  let ref_coeff = ref_number p.sc_mode in
  let bind_upper =
    if p.w_max = 0 then fun _ _ -> ()
    else fun solver fw -> solver#add_assertion (fw <=^ LI p.w_max)
  in
  object (x)
    inherit interpreter p
    method init : 't. (#context as 't) -> trs -> Dp.dg -> unit =
      fun solver trs dg ->
        let arg_mode =
	  let use_max = new enc_pos_info p.max_poly true in
	  let no_max = new enc_pos_info true false in
          match p.max_mode with
          | MAX_dup ->
            let t = maxpoly_heuristic trs dg (not p.max_poly) in
            fun f k -> t#info f (k-1)
          | MAX_all ->
            fun f _ -> if f#arity = 0 then no_max else use_max
          | MAX_none ->
            fun _ _ -> no_max
        in
	let c f k = "c_" ^ f#name ^ index k in
	let d f k = "d_" ^ f#name ^ index k in
	let w f = "w_" ^ f#name in
	let weight f i =
	  ref_weight (w f ^ coord i)
	in
	let coeff_sum f k i j =
	  if (arg_mode f k)#in_sum then
	    ref_coeff (c f k ^ coord i ^ coord j)
	  else
	    LI 0
	in
	let coeff_max f k i j =
	  if (arg_mode f k)#in_max then
	    ref_coeff (d f k ^ coord i ^ coord j)
	  else
	    LI 0
	in
        trs#iter_funs (fun f ->
          for i = 1 to p.w_dim do
              let w_i = w f ^ coord i in
              add_number p.w_mode solver w_i;
              solver#add_assertion (ref_weight w_i >=^ LI 0);
              for k = 1 to f#arity do
                let c_ki = c f k ^ coord i in
		let d_ki = d f k ^ coord i in
		if (arg_mode f k)#in_sum then
		  for j = 1 to p.w_dim do
		    let c_kij = c_ki ^ coord j in
		    add_number p.sc_mode solver c_kij;
		    bind_upper solver (ref_coeff c_kij);
		    if not p.dp && i = 1 then begin
		      solver#add_assertion (ref_coeff c_kij >=^ LI 1);
		    end else begin
		      solver#add_assertion (ref_coeff c_kij >=^ LI 0);
		    end
		  done;
		if (arg_mode f k)#in_max then
		  for j = 1 to p.w_dim do
		    let d_kij = d_ki ^ coord j in
		    add_number p.sc_mode solver d_kij;
		    bind_upper solver (ref_coeff d_kij);
		    solver#add_assertion (ref_coeff d_kij >=^ LI 0);
		  done;
              done
            done;
            Hashtbl.add table f#name {
              encodings = Array.map (fun i ->
		sum (
                  smt (weight f i) ::
		  max (
		    List.map (fun k ->
		      sum (
			List.map (fun j ->
			  prod [smt (coeff_max f k i j); bvar (k-1,j-1)]
		        ) (int_list 1 p.w_dim)
		      )
		    ) (int_list 1 f#arity)
		  ) ::
                  List.concat (
		    List.map (fun k ->
                      List.map (fun j ->
			prod [smt (coeff_sum f k i j); bvar (k-1,j-1)]
		      ) (int_list 1 p.w_dim)
                    ) (int_list 1 f#arity)
		  )
		)
	      ) (int_array 1 p.w_dim);
              pos_info = Array.map (
                fun k ->
		let ck = c f k in
                let con = solver#refer Bool (
                    smt_for_all (fun i ->
		      smt_for_all (fun j ->
		        (coeff_sum f k i j =^ LI 0) &^
		        (coeff_max f k i j =^ LI 0)
		      ) (int_list 1 p.w_dim)
                    ) (int_list 1 p.w_dim)
                  )
                in
                let ide =
                  smt_for_all (fun i ->
                    smt_for_all (fun j ->
		      coeff_sum f k i j =^ LI (if i = j then 1 else 0)
		    ) (int_list 1 p.w_dim) &^
                    (weight f i =^ LI 0)
                  ) (int_list 1 p.w_dim)
                in
		{
		  const = con;
                  id = ide;
                  weak_simple =
                    if p.w_neg then
                      smt_not con &^ smt_for_all (fun i ->
                        smt_for_all (fun j ->
                          coeff_max f k i j >=^ LI 1
                        ) (int_list 1 p.w_dim)
                      ) (int_list 1 p.w_dim)
                    else
                      smt_not con;
                }
              ) (int_array 1 f#arity);
            }
          )
  end


