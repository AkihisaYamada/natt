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
        punct_list (sub 1) (puts " + ") os es;
        if lvl > 1 then os#puts ")"
      end
    | Node(Mul, es) ->
      if es = [] then os#puts "1"
      else punct_list (sub 2) (puts " * ") os es
    | Node(Max, es) ->
      os#puts "max {"; punct_list (sub 0) (puts ", ") os es; os#puts "}";
    | Node(BVar v, []) -> var v os
  in
  sub 0 e

let eval_wexp solver =
  let rec sub (Node(f,ss)) =
    let ss = List.map sub ss in
    match f with
    | Smt exp -> wexp_smt (solver#get_value exp)
    | Add -> wexp_sum ss
    | Mul -> wexp_prod ss
    | Max -> wexp_max ss
    | _ -> Node(f,ss)
  in
  sub

(* Polynomial as a map from var list to coefficients *)

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
  smt_for_all (fun (vs,e2) -> et_find vs et1 >=^ e2) (StrListMap.bindings et2)

let et_order solver et1 et2 =
  let pre = (* tests >= for all coefficients but the constant part *)
    smt_for_all
        (fun (vs,e2) -> if vs = [] then LB true else et_find vs et1 >=^ e2)
        (StrListMap.bindings et2)
  in
  let pre = solver#refer Bool pre in
  let e1 = et_find [] et1 in
  let e2 = et_find [] et2 in
  (pre &^ (e1 >=^ e2), pre &^ (e1 >^ e2))

let put_et et pr =
  let init = ref true in
  StrListMap.iter (fun vs e ->
    if !init then init := false else pr#puts " + ";
    put_exp e pr; List.iter (fun v -> pr#puts "*"; pr#puts v) vs
  ) et


(* Max are expanded as lists *)

let ets_smt exp = [et_smt exp]

let ets_bvar name = [et_bvar name]

let ets_sum etss =
  List.map et_sum (list_product etss)

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

let put_ets ets pr =
  match ets with
  | [] -> pr#puts "oo";
  | [et] -> put_et et pr;
  | et::ets' -> pr#puts "max{"; put_et et pr; List.iter (fun et' -> pr#puts ", "; put_et et' pr;) ets'; pr#puts "}";

(* weight is array (vector) of such *)

type w_t = exp StrListMap.t list array

let put_w w pr =
  pr#puts "[ "; Array.map (fun ets -> put_ets ets pr; pr#puts "; ") w; pr#puts "]"

let add = Array.map2 (fun ets1 ets2 -> ets_sum [ets1;ets2])

let smult exp = Array.map (List.map (et_mul_one [] exp))

let order dim w1 w2 =
  Delay (fun solver ->
    let (ge,gt) = ets_order solver w1.(0) w2.(0) in
    let ge_rest =
      (smt_for_all (fun i -> ets_ge w1.(i) w2.(i)) (int_list 1 (dim-1)))
    in
    Cons(ge &^ ge_rest, gt)
  )

let index i = "_" ^ string_of_int i

let make_tri a b =
  smt_if a (smt_if b (LI 2) (LI 1)) (LI 0)

let make_quad a b =
  smt_if a (smt_if b (LI 3) (LI 2)) (smt_if b (LI 1) (LI 0))

let ref_number w_mode =
  match w_mode with
  | W_num -> fun v -> EV v
  | W_bool -> fun v -> smt_if (EV v) (LI 1) (LI 0)
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
  | W_arc -> fun solver v ->
    solver#add_variable_base v;
    solver#add_variable (v ^ "-b") Bool
  | W_none -> fun _ _ -> ()

type pos_info = {
  const : exp;
  strict_linear : exp;
  weak_simple : exp;
}
type sym_info = {
  encodings : (int * int) wsym term array;
  no_weight : exp;
  pos_info : pos_info array;
}

let coord i = (* makes suffix for coordination *)
  "_" ^ String.make 1 (char_of_int (int_of_char 'a' + i - 1))

let coord2 i j =
  "_" ^ String.make 1 (char_of_int (int_of_char 'a' + i - 1))
  ^ String.make 1 (char_of_int (int_of_char 'a' + j - 1))

class virtual interpreter p =
  let coord = if p.w_dim = 1 then fun _ -> "" else coord in
  let coord2 = if p.w_dim = 1 then fun _ _ -> "" else coord2 in
  let put_var = fun (k, i) -> puts ("x" ^ index (k+1) ^ coord (i+1)) in
  object (x)
    method virtual init : 't. (#context as 't) -> trs -> Dp.dg -> unit

    val table = Hashtbl.create 64

    method private find : 'b. (#sym as 'b) -> _ =
      fun f -> Hashtbl.find table f#name

    method no_weight : 'b. (#sym as 'b) -> exp =
      fun f -> (x#find f).no_weight

    method constant_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) is constant *)
      fun f k -> (x#find f).pos_info.(k-1).const

    method depend_on : 'b. (#sym as 'b) -> int -> exp =
      fun f k -> smt_not (x#constant_at f k)

    method strict_linear_at : 'b. (#sym as 'b) -> int -> exp =
      (* <--> [f](..x_k..) = x_k + ... *)
      fun f k -> (x#find f).pos_info.(k-1).strict_linear

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
      fun solver (Node(f,ss) as t) ->
      let ts = List.map (x#annotate solver) ss in
      let w = x#interpret f (List.map get_weight ts) in
      let w = Array.map (List.map (StrListMap.map solver#refer_base)) w in
      debug2 (endl << put_term t << puts " weight: " << put_w w);
      WT(f,ts,w)

    method output_sym :
      't 'o 'f. (#solver as 't) -> (#sym_detailed as 'f) -> (#printer as 'o) -> unit =
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

    method output_sym_template :
      'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
      fun f pr ->
      pr#puts "  ";
      f#output pr;
      let punct = ref ":\t[ " in
      Array.iteri (fun i wexp ->
        pr#puts !punct;
        punct := ",\n\t  ";
        put_wexp put_var wexp pr;
      ) (x#encode_sym f);
      pr#puts " ]"
  end

exception Continue

class template_mode s m = object
  val mutable in_sum : bool = s
  val mutable in_max : bool = m
  method set_sum b = in_sum <- b
  method set_max b = in_max <- b
  method in_sum = in_sum
  method in_max = in_max
end

class virtual template_heuristic =
object
  method virtual sym_mode : 'f. (#sym as 'f) -> template_mode
  method virtual arg_mode : 'f. (#sym as 'f) -> int -> template_mode
end

let sum_mode = new template_mode true false
let max_mode = new template_mode false true

let sum_heuristic =
object (x)
  inherit template_heuristic
  method sym_mode f = sum_mode
  method arg_mode f i = sum_mode
end;;

let max_heuristic =
object (x)
  inherit template_heuristic
  method sym_mode f = max_mode
  method arg_mode f i = max_mode
end;;

let maxpoly_heuristic (trs:trs) (dg:Dp.dg) either all =
object (x)
  inherit template_heuristic
  val sym_table : (string, template_mode) Hashtbl.t = Hashtbl.create 64
  val arg_table : (string, template_mode array) Hashtbl.t = Hashtbl.create 64

  method sym_mode f =
    try Hashtbl.find sym_table f#name
    with Not_found ->
      let ret = new template_mode true false in
      Hashtbl.add sym_table f#name ret;
      ret
  method private get_arg : 'f. (#sym as 'f) -> _ =
  fun f ->
    try Hashtbl.find arg_table f#name
    with Not_found ->
      let ret =
        Array.init (trs#find_sym f)#arity (fun k -> new template_mode true false)
      in
      Hashtbl.add arg_table f#name ret;
      ret
  method arg_mode f k = (x#get_arg f).(k-1)
  initializer
    let summarize_term test =
      let summarize_sym f =
        let sym = x#sym_mode f in
        let arg = x#get_arg f in
        let set_max i =
          arg.(i)#set_max true;
          sym#set_max true;
          if either then arg.(i)#set_sum false
        in
        let rec sub acc i = function
        | [] -> acc
        | vs::vss ->
          if arg.(i)#in_max then
            sub (Mset.join acc vs) (i+1) vss
          else
            let acc' = Mset.union acc vs in
            if test acc' then
              sub acc' (i+1) vss
            else (
              debug2 (puts "prefer max for " << puts f#name << puts " in " << put_int i << endl);
              if all then
                for j = 0 to i + List.length vss do
                  set_max j;
                done
              else
                set_max i;
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
    let iterer i rule =
      let lvs = summarize_term (fun _ -> true) rule#l in
      ignore (summarize_term (Mset.supseteq lvs) rule#r)
    in
    let rec loop () =
      try
        trs#iter_rules iterer;
        dg#iter_dps iterer;
      with Continue -> loop ()
    in
    loop ()
end;;


class pol_interpreter p =
  let coord = if p.w_dim = 1 then fun _ -> "" else coord in
  let coord2 = if p.w_dim = 1 then fun _ _ -> "" else coord2 in
  let ref_weight = ref_number p.w_mode in
  let ref_coeff = ref_number p.sc_mode in
  let bind_upper =
    if p.w_max = 0 then fun _ _ -> ()
    else fun solver fw -> solver#add_assertion (fw <=^ LI p.w_max)
  in
  let coord_params = Array.of_list p.w_params in
  object (x)
    inherit interpreter p
    method init : 't. (#context as 't) -> trs -> Dp.dg -> unit =
      fun solver trs dg ->
        let use_max = new template_mode p.max_poly true in
        let no_max = new template_mode true false in
        let use_dup t = t = TEMP_max_sum_dup || t = TEMP_sum_max_dup in
        let heuristic =
          if Array.exists use_dup coord_params then
            maxpoly_heuristic trs dg (not p.max_poly) true
          else sum_heuristic
        in
        let sym_mode f i =
          if f#arity < 2 && p.w_dim < 2 then no_max
          else
            let t = coord_params.(i-1) in
            if t = TEMP_max then use_max
            else if use_dup t then heuristic#sym_mode f
            else no_max
        in
        let arg_mode f k i =
          if f#arity < 2 && p.w_dim < 2 then no_max
          else
            let t = coord_params.(i-1) in
            if t = TEMP_max then use_max
            else if use_dup t then heuristic#arg_mode f k
            else no_max
        in
        let w f = "w_" ^ f#name in
        let c f k = "c_" ^ f#name ^ index k in
        let d f k = "d_" ^ f#name ^ index k in
        let a f k = "a_" ^ f#name ^ index k in
        let weight f i =
            ref_weight (w f ^ coord i)
        in
        let coeff_sum f k i j =
          if (arg_mode f k i)#in_sum then
            ref_coeff (c f k ^ coord2 i j) +^
            LI (if not p.dp && i = 1 && j = 1 then 1 else 0)
          else
            LI 0
        in
        let coeff_max f k i j =
          if (arg_mode f k i)#in_max then
            ref_coeff (d f k ^ coord2 i j) +^
            LI (if not p.dp && i = 1 && j = 1 then 1 else 0)
          else LI 0
        in
        let addend_max f k i j =
          if (arg_mode f k i)#in_max then ref_weight (a f k ^ coord2 i j)
          else LI 0
        in
        trs#iter_funs (fun f ->
          for i = 1 to p.w_dim do
            let w_i = w f ^ coord i in
            add_number p.w_mode solver w_i;
            if not p.w_neg || (f#arity = 0 && i = 1) then begin
              solver#add_assertion (ref_weight w_i >=^ LI 0);
            end;
            for k = 1 to f#arity do
              let c_k = c f k in
              let d_k = d f k in
              let a_k = a f k in
              if (arg_mode f k i)#in_sum then
                for j = 1 to p.w_dim do
                  let c_kij = c_k ^ coord2 i j in
                  add_number p.sc_mode solver c_kij;
                  bind_upper solver (ref_coeff c_kij);
                  solver#add_assertion (ref_coeff c_kij >=^ LI 0);
                done;
              if (arg_mode f k i)#in_max then
                for j = 1 to p.w_dim do
                  let d_kij = d_k ^ coord2 i j in
                  let a_kij = a_k ^ coord2 i j in
                  add_number p.sc_mode solver d_kij;
                  bind_upper solver (ref_coeff d_kij);
                  solver#add_assertion (ref_coeff d_kij >=^ LI 0);
                  add_number p.w_mode solver a_kij;
                  if not p.w_neg then begin
                    solver#add_assertion (ref_weight a_kij >=^ LI 0);
                  end;
                done;
              done
            done;
            Hashtbl.add table f#name {
              encodings = Array.map (fun i ->
                let w = wexp_smt (weight f i) in
                let added =
                  List.concat (
                    List.map (fun k ->
                      List.map (fun j ->
                        wexp_prod [wexp_smt (coeff_sum f k i j); wexp_bvar (k-1,j-1)]
                      ) (int_list 1 p.w_dim)
                    ) (int_list 1 f#arity)
                  )
                in
                let maxed =
                  List.concat (
                    List.map (fun k ->
                      List.concat (
                        List.map (fun j ->
                          let c = coeff_max f k i j in
                          if c = LI 0 then []
                          else
                            [ wexp_prod [
                                wexp_smt c;
                                wexp_sum [ wexp_smt (addend_max f k i j); wexp_bvar (k-1,j-1) ]
                              ]
                            ]
                        ) (int_list 1 p.w_dim)
                      )
                    ) (int_list 1 f#arity)
                  )
                in
                wexp_max (
                  (if p.w_neg && f#arity > 0 && i = 1 (* Only the first dimension need be positive *)
                   then [wexp_smt (LI 0)] else []) @
                  wexp_sum (w :: added) :: maxed
                )
              ) (int_array 1 p.w_dim);
              no_weight =
                smt_for_all (fun i ->
                  weight f i =^ LI 0 &^
                  smt_for_all (fun j ->
                    smt_for_all (fun k ->
                      addend_max f k i j =^ LI 0
                    ) (int_list 1 f#arity)
                  ) (int_list 1 p.w_dim)
                ) (int_list 1 p.w_dim);
              pos_info = Array.map (
                fun k ->
                let ck = c f k in
                let const = solver#refer Bool (
                    smt_for_all (fun i ->
                      smt_for_all (fun j ->
                        (coeff_sum f k i j =^ LI 0) &^
                        (coeff_max f k i j =^ LI 0)
                      ) (int_list 1 p.w_dim)
                    ) (int_list 1 p.w_dim)
                  )
                in
                let slin =
                  smt_for_all (fun i ->
                    smt_for_all (fun j ->
                      ( if (arg_mode f k i)#in_sum then coeff_sum f k i j
                        else coeff_max f k i j
                      ) =^ LI (if i = j then 1 else 0) &^
                      (addend_max f k i j =^ LI 0)
                    ) (int_list 1 p.w_dim) &^
                    (weight f i =^ LI 0)
                  ) (int_list 1 p.w_dim)
                in
                {
                  const = const;
                  strict_linear = slin;
                  weak_simple =
                    smt_for_all (fun i ->
                      (if p.w_neg then weight f i >=^ LI 0 else LB true) &^
                      ( (coeff_max f k i i >=^ LI 1) |^ (coeff_sum f k i i >=^ LI 1) )
                    ) (int_list 1 p.w_dim);
                }
              ) (int_array 1 f#arity);
            }
          );
debug (
  endl << puts "Weight template:" << endl <<
  (fun os ->
    trs#iter_funs (fun f ->
     x#output_sym_template f os;
     endl os
    )
  )
);
end


