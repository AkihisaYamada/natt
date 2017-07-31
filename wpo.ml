open Util
open Sym
open Term
open Trs
open Dp
open Smt
open Preorder
open Params
open Io
open Wpo_info

exception Continue

(* delete common elements from ss and ts *)
let delete_common =
  let rec sub ss1 ss ts =
    match ss with
    | [] -> ss1, ts
    | s :: ss ->
      match delete_one [] s ts with
      | Some ts -> sub ss1 ss ts
      | None -> sub (s::ss1) ss ts
  in
  sub []

class processor =
  (* SMT variables *)
  let mcw_v = "w" in
  let usable_v i = "u" ^ string_of_int i in
  let usable_w_v i = "uw" ^ string_of_int i in
  let usable_p_v i = "uP" ^ string_of_int i in
  let maxcons_v = "maxcons" in
  let gt_v i = "gt#" ^ string_of_int i in
  let ge_v i = "ge#" ^ string_of_int i in
  let gt_r_v i = "gt" ^ string_of_int i in
  let ge_r_v i = "ge" ^ string_of_int i in
  let gt_p_v i = "gtP" ^ string_of_int i in (* probabilistic rules *)
  let ge_p_v i = "geP" ^ string_of_int i in
  let supply_index v i = v ^ "_" ^ string_of_int i in
  let supply_index2 v j k = supply_index (supply_index v j) k in
  let makebin a b =
    smt_if a (smt_if b (LI 3) (LI 2)) (smt_if b (LI 1) (LI 0))
  in
  fun p (trs : trs) (estimator : Estimator.t) (dg : dg) ->
  let weight_ty =
    match p.base_ty with
    | TY_int -> Int
    | TY_real -> Real
  in
  (* Matrix interpretations *)
  let to_dim = intlist 1 p.w_dim in
  let makemat =
    if p.w_dim > 1 then
      fun f -> Mat(List.map (fun j -> List.map (fun k -> f j k) to_dim) to_dim)
    else
      fun f -> f 1 1
  in
  let makevec =
    if p.w_dim > 1 then
      fun f -> Vec(List.map f to_dim)
    else
      fun f -> f 1
  in
  let supply_matrix_index = if p.w_dim > 1 then supply_index2 else fun v _ _ -> v in

  let usables = ref [] in
  let dplist = ref [] in
  let solver =
    let (tool,options) = p.smt_tool in
    create_solver p.peek_to p.peek_in p.peek_out tool options
  in
  let () = solver#set_base_ty weight_ty in
  (* Signature as the set of function symbols with their informations. *)
  let sigma : (string,wpo_sym) Hashtbl.t = Hashtbl.create 256 in
  let lookup_name name =
    try Hashtbl.find sigma name with  _ -> raise (Internal name)
  in
  let lookup f = lookup_name f#name in
  let nest_map = ref Mset.empty in
  let nest fname = Mset.count fname !nest_map in

(*** Weights ***)
  let add_number w_mode =
    match w_mode with
    | W_num -> fun v -> solver#new_variable v weight_ty
    | W_bool -> fun v -> PB(solver#new_variable v Bool)
    | W_tri -> fun v ->
      smt_if (solver#new_variable (v ^ "a") Bool)
        (smt_if (solver#new_variable (v ^ "b") Bool) (LI 2) (LI 1))
        (LI 0)
    | W_quad -> fun v ->
      makebin (solver#new_variable (v ^ "a") Bool) (solver#new_variable (v ^ "b") Bool)
    | W_none -> fun _ -> LI 0
  in
  (* Minimum weight *)
  let mcw_val = LI p.mcw_val in
  let mcw =
    match p.mcw_mode with
    | MCW_num -> EV mcw_v
    | MCW_bool  -> PB(EV mcw_v)
    | MCW_const -> mcw_val
  in
  (* constant part *)
  let add_weight =
    let bind_lower =
      if p.w_neg then
        if p.w_max = 0 then fun _ _ -> ()
        else fun _ fw -> solver#add_assertion (fw >=^ LI (- p.w_max))
      else fun finfo fw -> solver#add_assertion (fw >=^ if finfo#base#arity = 0 then mcw else LI 0)
    in
    let bind_upper =
      if p.w_max = 0 then fun _ _ -> ()
      else fun _ fw -> solver#add_assertion (fw <=^ LI p.w_max)
    in
    let sub finfo v i =
      let fw = add_number p.w_mode (v i) in
      bind_lower finfo fw;
      bind_upper finfo fw;
      fw
    in
    fun fname finfo ->
      if not p.ac_w && finfo#base#is_associative then begin
        finfo#set_weight (LI 0)
      end else begin
        let v =
          if p.w_dim > 1 then supply_index ("w_" ^ fname)
          else k_comb ("w_" ^ fname)
        in
        finfo#set_weight (makevec (sub finfo v));
      end;
  in

  (* Coefficients *)
  let add_subterm_coef =
    match p.sc_mode with
    | W_none -> fun fname finfo ->
      finfo#set_subterm_coef (k_comb (LI 0))
    | _ ->
      let coef_default v j k =
        let coef = add_number p.sc_mode (supply_matrix_index v j k) in
        (* Additional constraints *)
        if not p.dp && j = 1 && k = 1 then
          (* if not in DP mode, assert top left element >= 1 *)
          if p.sc_mode = W_num then (
            solver#add_assertion (coef >=^ LI 1);
            if p.sc_max > 0 then
              solver#add_assertion (coef <=^ LI (p.sc_max + 1));
            coef
          ) else (* Just add 1 *)
            coef +^ LI 1
        else (
          solver#add_assertion (coef >=^ LI 0);
          if p.sc_max > 0 then
            solver#add_assertion (coef <=^ LI p.sc_max);
          coef
        )
      in
      let coef =
        match p.mat_mode with
        | MAT_full  -> fun _ -> coef_default
        | MAT_upper -> fun finfo v j k ->
          if finfo#base#is_defined || j < k then
            coef_default v j k
          else if j = k then
            if j = 1 then LI 1
            else add_number W_bool (supply_matrix_index v j k)
          else LI 0
        | MAT_lower -> fun finfo v j k ->
          if finfo#base#is_defined || j > k then
            coef_default v j k
          else if j = k then
            if j = 1 then LI 1
            else add_number W_bool (supply_matrix_index v j k)
          else LI 0
      in
      fun fname finfo ->
        match finfo#base#ty with
        | Th "C" ->
          finfo#set_subterm_coef (k_comb (makemat (coef finfo ("sc_" ^ fname))));
        | Th "A" | Th "AC" ->
          let coef =
            if not p.dp || p.sc_mode = W_none then
              LI 1
            else
              PB(solver#new_variable ("sc_" ^ fname) Bool)
          in
          finfo#set_subterm_coef (k_comb coef)
        | _ ->
          let n = finfo#base#arity in
          let v = (if n > 1 then supply_index else k_comb) ("sc_" ^ fname) in
          let array = Array.make n (LI 0) in
          for i = 1 to n do
            array.(i-1) <- makemat (coef finfo (v i));
          done;
          finfo#set_subterm_coef (fun i -> array.(i-1));
    in

  (* Max-polynomial *)
  let add_subterm_penalty fname finfo =
    if finfo#max then begin
      let sub v j k =
        let pen = add_number p.sp_mode (supply_matrix_index v j k) in
        if not p.w_neg then solver#add_assertion (pen >=^ LI 0);
        if p.w_max > 0 then solver#add_assertion (pen <=^ LI p.w_max);
        pen
      in
      let use_maxpol () =
        finfo#set_sum true;
        debug2 (puts "    using maxpol for " << puts fname << endl);
      in
      match finfo#base#ty with
      | Th "C" ->
        if p.Params.max_poly &&
          (p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
        then begin
          finfo#set_subterm_penalty (k_comb (makemat (sub ("sp_" ^ fname))));
          finfo#set_maxfilt (k_comb (solver#new_variable ("maxfilt_" ^ fname) Bool));
          use_maxpol ();
        end else begin
          finfo#set_sum false;
          finfo#set_maxfilt (fun i -> finfo#subterm_coef i <>^ LI 0);
        end;
      | Th "A" | Th "AC" ->
        if p.Params.max_poly &&
          (p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
        then begin
          finfo#set_maxfilt (k_comb (solver#new_variable ("maxfilt_" ^ fname) Bool));
          use_maxpol ();
        end else begin
          finfo#set_sum false;
          finfo#set_maxfilt (fun i -> finfo#subterm_coef i <>^ LI 0);
        end;
      | _ ->
        let n = finfo#base#arity in
        let vsp = (if n > 1 then supply_index else k_comb) ("sp_" ^ fname) in
        let array = Array.make n (LI 0) in
        for i = 1 to n do
          array.(i-1) <- makemat (sub (vsp i));
        done;
        finfo#set_subterm_penalty (fun i -> array.(i-1));
        if p.Params.max_poly &&
          (p.max_poly_nest = 0 || nest fname <= p.max_poly_nest)
        then begin
          let vmf = (if n > 1 then supply_index else k_comb) ("maxfilt_" ^ fname) in
          let emf i = EV(vmf i) in
          for i = 1 to n do
            solver#add_variable (vmf i) Bool;
          done;
          use_maxpol ();
          finfo#set_maxfilt emf;
        end else begin
          finfo#set_sum false;
          finfo#set_maxfilt (fun i -> finfo#subterm_coef i <>^ LI 0);
        end;
    end;
  in

  (* accumulation of coeficient for term variables *)
  let vc_lookup vc vname =
    try Hashtbl.find vc vname with Not_found -> LI 0
  in
  let vc_cond vc1 vc2 =
    let comp vname value e = (vc_lookup vc1 vname >=^ value) &^ e in
    Hashtbl.fold comp vc2 (LB true)
  in
  let vc_merge_one vc coef vname value =
    Hashtbl.replace vc vname (vc_lookup vc vname +^ (coef *^ value))
  in
  let vc_mul_add vc1 coef vc2 =
    Hashtbl.iter (vc_merge_one vc1 coef) vc2
  in
  let vc_mul vc coef =
    Hashtbl.iter (fun vname value -> Hashtbl.replace vc vname (coef *^ value)) vc
  in
  let vc_refer context vc =
    Hashtbl.iter (fun vname value -> Hashtbl.replace vc vname (context#refer_base value)) vc
  in

  (* weight order *)
  let polo (vc1,e1) (vc2,e2) =
    smt_if (vc_cond vc1 vc2) (smt_order e1 e2) not_ordered
  in
  let wo =
    if p.w_mode = W_none then
      fun _ _ -> weakly_ordered
    else
      let rec sub2 ge gt ws1 w2 =
        if gt = LB true then (gt,gt)
        else
          match ws1 with
          | [] -> (ge,gt)
          | w1::ws1 ->
            let (curr_ge,curr_gt) = split (polo w1 w2) solver in
            sub2 (ge |^ curr_ge) (gt |^ curr_gt) ws1 w2
      in
      let rec sub ge gt ws1 ws2 =
        if ge = LB false then not_ordered
        else
          match ws2 with
          | [] ->
            Cons(ge,gt)
          | w2::ws2 ->
            let (curr_ge,curr_gt) = sub2 (LB false) (LB false) ws1 w2 in
            sub (ge &^ curr_ge) (gt &^ curr_gt) ws1 ws2
      in
      fun ws1 ws2 ->
      match ws1, ws2 with
      | [w1], [w2] -> polo w1 w2
      | _ -> sub (LB true) (LB true) ws1 ws2
  in

(*** Maximum constant ***)
  let maxcons = if p.maxcons then EV(maxcons_v) else LB false in

(*** Precedence ***)
  let pmin = LI 0 in
  let pmax = ref (LI 0) in
  let add_prec_default fname finfo =
    let fp = solver#new_variable ("p_" ^ fname) weight_ty in
    finfo#set_prec fp;
    solver#add_assertion (pmin <=^ fp);
    solver#add_assertion (fp <=^ !pmax);
  in
  let add_prec_ac fname finfo =
    if marked_name fname then begin
      (* marked AC symbols have the precedence of unmarked one *)
    end else begin
      add_prec_default fname finfo;
    end;
  in
  let add_prec =
    match p.prec_mode with
    | PREC_none -> fun _ _ -> ()
    | _ -> fun fname finfo ->
      (if finfo#base#is_associative then add_prec_ac else add_prec_default) fname finfo
  in
  (* Precedence over symbols *)
  let spo =
    match p.prec_mode with
    | PREC_none -> fun _ _ -> weakly_ordered
    | PREC_quasi ->
      fun finfo ginfo ->
        let pf = finfo#prec in
        let pg = ginfo#prec in
        Cons(pf =^ pg, pf >^ pg)
    | _ ->
      fun finfo ginfo ->
        let pf = finfo#prec in
        let pg = ginfo#prec in
        if pf = pg then weakly_ordered else Cons(LB false, pf >^ pg)
  in
  (* Precedence of root symbols *)
  let po =
    let sub =
      if p.mincons then
        fun g ts -> Cons((if ts = [] then pmin =^ (lookup g)#prec else LB false), LB false)
      else
        fun _ _ -> not_ordered
    in
    fun (WT((f:#sym),_,_)) (WT((g:#sym),ts,_)) ->
      if f#is_var then
        if g#is_var then Cons(LB(f#equals g), LB false)
        else sub g ts
      else if g#is_var then not_ordered
      else spo (lookup f) (lookup g)
  in

(*** Argument filters ***)
  let add_argfilt =
    (* argument is filtered iff coef = 0 *)
    if not p.dp || p.sc_mode = W_none then
      fun _ finfo ->
        finfo#set_argfilt (k_comb (LB true));
    else if p.sc_mode = W_bool && p.w_dim = 1 && not p.Params.max_poly then
      fun _ finfo ->
        finfo#set_argfilt (fun i -> finfo#subterm_coef i <>^ LI 0);
    else
      (* give an alias for coef <> 0 *)
      let iterer =
        if p.Params.max_poly then
          fun finfo vf i ->
            solver#add_definition (vf i) Bool
            ( (finfo#subterm_coef i <>^ LI 0) |^ 
              if finfo#max then finfo#maxfilt i else LB false
            );
        else
          fun finfo vf i ->
            solver#add_definition (vf i) Bool (finfo#subterm_coef i <>^ LI 0);
      in
      fun fname finfo ->
        let v = "af_" ^ fname in
        match finfo#base#ty with
        | Fun | Th "A" ->
          let vf i = supply_index v i in
          let ef i = EV(vf i) in
          for i = 1 to finfo#base#arity do
            iterer finfo vf i;
          done;
          finfo#set_argfilt ef;
        | Th "AC" | Th "C" ->
          let vf _ = v in
          let ef _ = EV(v) in
          iterer finfo vf 1;
          finfo#set_argfilt ef;
        | _ -> ()
  in
  (* collapsing argument filters *)
  let add_collapse =
    if p.collapse then
      fun fname finfo to_n ->
        let v = "col_" ^ fname in
        solver#add_variable v Bool;
        finfo#set_collapse (EV v);
        solver#add_assertion (EV v =>^ ES1(List.map finfo#argfilt to_n));
    else
      fun _ finfo _ -> finfo#set_collapse (LB false)
  in

(*** Usable rules ***)
  let usable =
    if (if p.dp then dg#minimal && p.usable else not p.remove_all) then
      fun i -> EV(usable_v i)
    else
      k_comb (LB true)
  in
  let usable_w =
    if p.dp && p.usable_w then
      fun i -> EV(usable_w_v i)
    else
      usable
  in
  let usable_p =
    if (if p.dp then dg#minimal && p.usable else not p.remove_all) then
      fun i -> EV(usable_p_v i)
    else
      k_comb (LB true)
  in
  let rec set_usable filt usable s =
    smt_for_all usable (estimator#find_matchable s) &^ set_usable_inner filt usable s
  and set_usable_inner filt usable (Node(f,ss)) =
    if f#is_var then
      smt_for_all (set_usable_inner filt usable) ss
    else
      let finfo = lookup f in
      let rec sub i ss =
        match ss with
        | [] -> LB true
        | s::ss -> (filt finfo i =>^ set_usable filt usable s) &^ sub (i+1) ss
      in
      sub 1 ss
  in
  let add_usable =
    if (if p.dp then not p.usable else p.remove_all) then
      fun _ -> ()
    else
      fun i ->
        solver#add_variable (usable_v i) Bool;
        if p.usable_w then
          solver#add_variable (usable_w_v i) Bool;
  in
  let add_usable_p =
    if (if p.dp then not p.usable else p.remove_all) then
      fun _ -> ()
    else
      fun i ->
        solver#add_variable (usable_p_v i) Bool;
  in

(*** Status ***)
  let add_perm =
    let sub_lex =
      let sub_perm fname finfo n =
        match finfo#status_mode with
        | S_empty -> finfo#set_perm (fun _ _ -> LB false)
        | S_none -> finfo#set_perm (fun i k -> LB(i = k) &^ finfo#argfilt i)
        | _ ->
          if finfo#status_mode = S_total && n = 1 then begin
            finfo#set_perm (k_comb finfo#argfilt);
          end else begin
            let perm_v i k = supply_index (supply_index ("st_" ^ fname) i) k in
            let perm_e i k = EV(perm_v i k) in
            for i = 1 to n do
              for k = 1 to n do
                solver#add_variable (perm_v i k) Bool;
              done;
            done;
            finfo#set_perm perm_e;
          end;
      in
      let sub_permed fname finfo n =
        match finfo#status_mode with
        | S_empty ->
          finfo#set_permed (fun i -> LB false)
        | S_partial ->
          let permed_v i = supply_index ("permed_" ^ fname) i in
          let permed_e i = EV(permed_v i) in
          for i = 1 to n do
            solver#add_variable (permed_v i) Bool;
          done;
          finfo#set_permed permed_e;
        | _ -> finfo#set_permed finfo#argfilt;
      in
      let sub_mapped fname finfo n to_n =
        match finfo#status_mode with
        | S_empty -> finfo#set_mapped (k_comb (LB false));
        | S_none -> finfo#set_mapped finfo#argfilt;
        | _ ->
          if p.dp && (p.sc_mode <> W_none || finfo#status_mode = S_partial) then
            let mapped_v k = supply_index ("mapped_" ^ fname) k in
            let mapped_e k = EV(mapped_v k) in
            for k = 1 to n do
              solver#add_variable (mapped_v k) Bool;
            done;
            solver#add_assertion (OD (List.map mapped_e to_n));
            finfo#set_mapped mapped_e;
          else
            finfo#set_mapped (k_comb (LB true))
      in
      fun fname finfo n to_n ->
        sub_perm fname finfo n;
        sub_permed fname finfo n;
        sub_mapped fname finfo n to_n;
        for i = 1 to n do
          let p_i = finfo#permed i in
          if p.status_copy then begin
            for j = 1 to n do
              solver#add_assertion (finfo#perm i j =>^ p_i);
            done;
            solver#add_assertion (p_i =>^ smt_exists (finfo#perm i) to_n);
          end else begin
            let (zero,one) = split (ZeroOne (List.map (finfo#perm i) to_n)) solver in
            solver#add_assertion (p_i =>^ one);
            solver#add_assertion (p_i |^ zero);
          end;
          let m_i = finfo#mapped i in
          let mapper j = finfo#perm j i in
          let (zero,one) = split (ZeroOne (List.map mapper to_n)) solver in
          solver#add_assertion (m_i =>^ one);
          solver#add_assertion (m_i |^ zero);
        done;
    in
    let sub_c =
      let sub_perm finfo =
        finfo#set_perm (
        match finfo#status_mode with
        | S_empty -> k_comb (k_comb (LB false))
        | S_partial -> fun i j -> if i = j then finfo#permed i else LB false
        | _ -> fun i j -> if i = j then finfo#argfilt i else LB false
        )
      in
      let sub_permed fname finfo =
        match finfo#status_mode with
        | S_empty -> finfo#set_permed (k_comb (LB false));
        | S_partial ->
          let permed_v = "permed_" ^ fname in
          let permed_e _ = EV(permed_v) in
          solver#add_variable permed_v Bool;
          finfo#set_permed permed_e;
        | _ ->
          finfo#set_permed finfo#argfilt;
      in
      fun fname finfo ->
        sub_perm finfo;
        sub_permed fname finfo;
        finfo#set_mapped finfo#permed;
    in
    fun fname finfo to_n ->
      finfo#set_status_mode
        (if p.status_nest > 0 && nest fname > p.status_nest then S_empty
         else p.Params.status_mode);
      match finfo#base#ty with
      | Th th ->
        if (p.max_mode <> MAX_all || p.sp_mode <> W_none) &&
          (th = "A" || th = "AC") &&
          finfo#max
        then begin
          (* in this case, we cannot ensure monotonicity... *)
          finfo#set_status_mode S_empty;
        end;
        if th = "C" || th = "AC" then begin
          sub_c fname finfo;
        end else begin
          sub_lex fname finfo finfo#base#arity to_n;
        end;
      | _ -> sub_lex fname finfo finfo#base#arity to_n;
  in

  let add_mset_status =
    let sub =
      if not p.ext_mset then
        fun _ -> LB false
      else if p.ext_lex then
        fun fname -> solver#new_variable ("mset_" ^ fname) Bool
      else
        fun _ -> LB true
    in
    fun fname finfo ->
      match finfo#base#ty with
      | Th "C"
      | Th "AC" -> finfo#set_mset_status (LB true);
      | _ -> if finfo#base#arity > 1 then finfo#set_mset_status (sub fname);
  in

(*** Tests for arity ***)
  let is_unary =
    if p.dp && p.sc_mode <> W_none then
      fun finfo to_n ->
        smt_not finfo#collapse &^ ES1(List.map finfo#argfilt to_n)
    else
      fun _ -> function [_] -> LB true | _ -> LB false
  in

(*** preparing for function symbols ***)
  let add_symbol fname (finfo:wpo_sym) =
    let n = finfo#base#arity in
    let to_n = intlist 1 n in

    add_weight fname finfo;

    add_subterm_coef fname finfo;
    add_subterm_penalty fname finfo;

    add_argfilt fname finfo;
    add_collapse fname finfo to_n;

    add_prec fname finfo;

    add_perm fname finfo to_n;

    (* for status *)
    add_mset_status fname finfo;

    let col = finfo#collapse in
    let fw = finfo#weight in
    let fp = finfo#prec in

    (* if $\pi(f)$ is collapsing, then $w(f) = 0$ *)
    solver#add_assertion (col =>^ (fw =^ LI 0));

    for i = 1 to n do
      let pi = finfo#permed i in
      let coef = finfo#subterm_coef i in
      let maxf = finfo#maxfilt i in
      let pen = finfo#subterm_penalty i in

      (* permed position must be weakly monotone *)
      solver#add_assertion (smt_not pi |^ (coef >=^ LI 1) |^ maxf);

      (* permed position must be a simple position *)
      if p.w_neg then begin
        solver#add_assertion (pi =>^ (fw >=^ LI 0));
        solver#add_assertion (pi =>^ (pen >=^ LI 0));
      end;

      (* collapsing filter *)
      solver#add_assertion (col &^ finfo#argfilt i =>^ pi);
      solver#add_assertion (col &^ pi =>^ (coef =^ LI 1));
      solver#add_assertion (col &^ pi =>^ (maxf &^ (pen =^ LI 0)));
    done;
    if n > 0 && p.dp && p.sc_mode <> W_none &&
      (p.w_neg || p.adm || p.maxcons || p.mincons || p.mcw_val > 0)
    then begin
      let v = "const_" ^ fname in
      solver#add_definition v Bool
        (smt_not col &^ smt_for_all (fun i -> smt_not (finfo#argfilt i)) to_n);
      finfo#set_is_const (EV v);
      if finfo#status_mode = S_partial && (p.mincons || p.maxcons) then begin
        let v = "qconst_" ^ fname in
        solver#add_definition v Bool
          (smt_not col &^ smt_for_all (fun i -> smt_not (finfo#permed i)) to_n);
        finfo#set_is_quasi_const (EV v);
      end else begin
        finfo#set_is_quasi_const (EV v);
      end;
    end;

    if p.w_neg || p.mcw_val > 0 then
      (* asserting $mcw$ be the minimal weight of constants. *)
      if finfo#max then
        solver#add_assertion (fw >=^ mcw)
      else
        solver#add_assertion (finfo#is_const =>^ (fw >=^ mcw));

    if p.adm then begin
      if finfo#max then
        for i = 1 to n do
          solver#add_assertion (finfo#argfilt i =>^ (finfo#subterm_penalty i >^ LI 0));
        done
      else if p.mcw_val = 0 then
        solver#add_assertion (finfo#is_const |^ (fw >^ LI 0))
      else begin
        solver#add_assertion (fp <=^ !pmax);
        (* asserting admissibility of weight and precedence. *)
        solver#add_assertion
          (smt_if (is_unary finfo to_n &^ (fw =^ LI 0)) (fp =^ !pmax) (fp <^ !pmax));
      end;
    end else if p.maxcons then begin
      solver#add_assertion (fp <=^ !pmax);
    end;

    let qc = finfo#is_quasi_const in
    if p.mincons then begin
      solver#add_assertion (qc =>^ (fp >=^ pmin));
    end;
    if p.maxcons then begin
      (* if maxcons is true, then only quasi-constant can have the maximum precedence *)
      solver#add_assertion (smt_not maxcons |^ qc |^ (fp <^ !pmax));
      if not p.adm then begin
        let strictly_simple =
          if finfo#max then
            smt_for_all (fun i -> finfo#subterm_penalty i >^ LI 0) to_n
          else
            fw >^ LI 0
        in
        solver#add_assertion (smt_not maxcons |^ qc |^ col |^ strictly_simple);
      end;
    end;
  in

(* for weight computation *)
  let refer_w =
    if p.refer_w then
      solver#refer_base
    else
      fun x -> x
  in
  let emptytbl = Hashtbl.create 0 in
  let weight_summand fty finfo =
    let rec sub_ac coef vc w i e =
      function
      | [] -> (vc, w +^ coef *^ (e +^ (LI i *^ w)))
      | (vc',e')::vws ->
        vc_mul_add vc coef vc';
        sub_ac coef vc w (i + 1) (e +^ e') vws
    in
    let rec sub_c coef vc w e =
      function
      | [] -> (vc, w +^ (coef *^ e))
      | (vc',e')::vws ->
        vc_mul_add vc coef vc';
        sub_c coef vc w (e +^ e') vws
    in
    let rec sub_lex coef i vc e =
      function
      | [] -> (vc,e)
      | (vc',e')::vws ->
        let c = coef i in
        vc_mul_add vc c vc';
        sub_lex coef (i + 1) vc (e +^ (c *^ e')) vws
    in
    let sub =
      function
      | []  -> (emptytbl, finfo#weight)
      | vces  ->
        let vc = Hashtbl.create 4 in
        let (vc,e) =
          match fty with
          | Th "AC"
          | Th "A"  -> sub_ac (finfo#subterm_coef 1) vc finfo#weight (-2) (LI 0) vces
          | Th "C"  -> sub_c  (finfo#subterm_coef 1) vc finfo#weight (LI 0) vces
          | _       -> sub_lex (finfo#subterm_coef) 1 vc finfo#weight vces
        in
        vc_refer solver vc;
        (vc, refer_w e)
    in
    List.map sub
  in
  let weight_var f argws =
    if argws <> [] then raise (Internal "higher order variable");
    let vc = Hashtbl.create 1 in
    vc_merge_one vc (LI 1) f#name (LI 1);
    [(vc,mcw)]
  in
  let weight_max =
    let folder af sp ret (vc,e) =
      if af = LB true then
        (vc, solver#refer_base (sp +^ e))::ret
      else
        let vc' = Hashtbl.copy vc in
        vc_mul vc' (smt_pb af);
        vc_refer solver vc';
        (vc', solver#refer_base (smt_pb af *^ (sp +^ e)))::ret
    in
    let rec sub_fun finfo i ret =
      function
      | []      -> ret
      | ws::wss ->
        let mf = finfo#maxfilt i in
        let sp = finfo#subterm_penalty i in
        sub_fun finfo (i + 1) (List.fold_left (folder mf sp) ret ws) wss
    in
    let sub_c finfo =
      let mf = finfo#maxfilt 1 in
      let sp = finfo#subterm_penalty 1 in
      let rec sub ret =
        function
        | []      -> ret
        | ws::wss -> sub (List.fold_left (folder mf sp) ret ws) wss
      in
      sub
    in
    let sub_ac finfo =
      let mf = finfo#maxfilt 1 in
      let rec sub ret =
        function
        | []      -> ret
        | ws::wss -> sub (List.fold_left (folder mf (LI 0)) ret ws) wss
      in
      sub
    in
    match p.max_mode with
    | MAX_none ->
      if p.w_neg then
        fun f argws ->
          if f#is_var then weight_var f argws
          else
            (* make it lower bounded by mcw *)
            let sum = weight_summand f#ty (lookup f) (list_product argws) in
            if argws = [] then sum else (emptytbl,mcw)::sum
      else
        fun f argws ->
          if f#is_var then weight_var f argws
          else weight_summand f#ty (lookup f) (list_product argws)
    | _ ->
      fun f argws ->
        if f#is_var then weight_var f argws
        else
          let finfo = lookup f in
          if finfo#max then
            let init =
              if finfo#sum then
                weight_summand f#ty finfo (list_product argws)
              else if p.w_neg then
                (* make it lower bounded by mcw *)
                [emptytbl,mcw]
              else []
            in
            match f#ty with
            | Th "C" -> sub_c finfo init argws
            | Th "AC" -> sub_ac finfo init argws
            | _ -> sub_fun finfo 1 init argws
          else
            let sum = weight_summand f#ty finfo (list_product argws) in
            if p.w_neg && argws <> [] then
              (* make it lower bounded by mcw *)
              (emptytbl,mcw)::sum
            else sum
  in
  (* annote terms with weights *)
  let rec annote (Node(f,ss)) =
    let ss =
      match f#ty with
      | Th "AC" -> local_flat f ss
      | _ -> ss
    in
    let args = List.map annote ss in
    let argws = List.map get_weight args in
    let ws = weight_max f argws in
    WT(f, args, ws)
  in

(*** argument comparison ***)
  let lexperm_compargs =
    match p.Params.status_mode with
    | S_empty ->
      fun _ _ _ _ _ -> weakly_ordered
    | S_none ->
      if p.dp && p.sc_mode <> W_none then
        if p.prec_mode = PREC_quasi then
          raise (No_support "quasi-precedence + 0-coefficient + no status")
        else
          fun finfo ginfo order ss ts ->
            if finfo == ginfo then
              filtered_lex_extension finfo#permed order ss ts
            else not_ordered
      else
        (* simple lexicographic extension is used. *)
        fun _ _ -> lex_extension
    | _ ->
      if p.prec_mode = PREC_quasi then
        fun finfo ginfo ->
          if finfo == ginfo then
            permuted_lex_extension finfo#perm finfo#mapped
          else
            permuted_lex_extension2 finfo#perm ginfo#perm finfo#mapped ginfo#mapped
      else
        fun finfo ginfo ->
          if finfo == ginfo then
            permuted_lex_extension finfo#perm finfo#mapped
          else
            fun _ _ _ -> not_ordered
  in

  let statused_compargs finfo ginfo order ss ts =
    match ss, ts with
    | [], []  -> weakly_ordered
    | [], _   -> Cons(ginfo#is_quasi_const, LB false)
    | _, []   -> Cons(LB true, smt_not finfo#is_quasi_const)
    | _ ->
      Delay
      (fun context ->
        let (lge,lgt) =
          split (lexperm_compargs finfo ginfo order ss ts) context
        in
        let (mge,mgt) =
          split (filtered_mset_extension finfo#permed ginfo#permed order ss ts) context
        in
        Cons
        ( (finfo#mset_status &^ ginfo#mset_status &^ mge) |^
          (finfo#lex_status  &^ ginfo#lex_status  &^ lge),
          (finfo#mset_status &^ ginfo#mset_status &^ mgt) |^
          (finfo#lex_status  &^ ginfo#lex_status  &^ lgt)
        )
      )
  in
  (* compargs for normal function symbols *)
  let default_compargs =
    if p.ext_mset then
      if p.ext_lex then
        statused_compargs
      else
        fun finfo ginfo -> filtered_mset_extension finfo#permed ginfo#permed
    else if p.ext_lex then
      lexperm_compargs
    else
      fun _ _ _ _ _ -> weakly_ordered
  in

(*** compargs for AC symbols ***)

  let small_head spo hinfo (WT(f,_,_)) =
    if f#is_var then LB false else strictly (spo hinfo (lookup f))
  in
  let no_small_head spo hinfo s = smt_not (small_head spo hinfo s) in
  let delete_variables =
    let rec sub ss1 =
      function
      | []  -> ss1
      | WT(f,_,_) as s :: ss ->
        if f#is_var then sub ss1 ss else sub (s::ss1) ss
    in
    sub []
  in

  let comparg_ac finfo order ss ts =
    let ss, ts = delete_common ss ts in
    let nss = List.length ss in
    let nts = List.length ts in
    (* variables in ss may not contribute to other than length *)
    let ss = delete_variables ss in
    (* for efficiency *)
    let nxs = List.length ss in
    let nys = nts in
    let xa = Array.of_list ss in
    let ya = Array.of_list ts in
    let compa = Array.init nxs
      (fun i -> Array.init nys
        (fun j -> solver#refer (Prod(Bool,Bool)) (order xa.(i) ya.(j)))
      )
    in
    compose
    (
      let ifilter i = no_small_head spo finfo xa.(i-1) in
      let jfilter j = no_small_head spo finfo ya.(j-1) in
      filtered_mset_extension_body ifilter jfilter nxs nys compa
    )
    (
      if nss > nts then
        strictly_ordered
      else if nss < nts then
        not_ordered
      else
        let ifilter i = small_head spo finfo xa.(i-1) in
        let jfilter j = small_head spo finfo ya.(j-1) in
        filtered_mset_extension_body ifilter jfilter nxs nys compa
    )
  in
  (* For AC-RPO.
   * $(cw,cs,ts) \in emb_candidates f ss$ indicates that f(ts) is
   * a strict embedding of \pi(f(ss)) if cs && cw holds, and
   * \pi(f(ss)) iteself if not cs but cw.
   *)
  let emb_candidates fname =
    let rec sub precond preargs ret postargs =
      if precond = LB false then ret else
      match postargs with
      | [] ->
        (* the whole argument is \pi(f(ss)) if the precondition holds *)
        (precond, LB false, preargs) :: ret
      | (WT(g,ts,_) as t)::ss ->
        if fname = g#name then
          (* this argument should be flattened *)
          sub precond preargs ret (ts @ ss)
        else (
        let mapper (tcw,tcs,ts') = (tcw,tcs,ts' @ [t]) in
        let ret = List.map mapper ret in
        if g#is_var then
          (* a variable must remain *)
          sub precond (preargs @ [t]) ret ss
        else
          let ginfo = lookup g in
          let p_g = ginfo#permed in
          let afl_g = smt_not ginfo#collapse in
          (* pop-out an argument *)
          let precond = solver#refer Bool precond in
          let ret = sub2 precond preargs ret afl_g p_g 1 ts in
          (* t may remain, only if its root symbol is not collapsed *)
          sub (precond &^ afl_g) (preargs @ [t]) ret ss
      )
    and sub2 precond preargs ret afl_g p_g i =
      function
      | [] -> ret
      | (WT(h,vs,_) as u)::us ->
        (* If u survives after argfilter, then it can pop out.
           If moreover g survives, then the pop-out is strict embedding.
         *)
        let ret =
          (precond &^ p_g i, afl_g, preargs @ (if h#name = fname then vs else [u])) :: ret
        in
        sub2 precond preargs ret afl_g p_g (i+1) us
    in
    sub (LB true) [] []
  in

  let rec ac_rpo_compargs fname finfo ss ts order =
    Delay (fun context ->
      let mapper (scw,scs,ss') =
        (context#refer Bool scw, context#refer Bool scs, ss')
      in
      let sss = List.map mapper (emb_candidates fname ss) in
      let tss = List.map mapper (emb_candidates fname ts) in

      let rec step2 ge gt ss' tss =
      match tss with
      | [] ->
        (* ge to all proper embedding is a condition for gt *)
        (ge, ge &^ gt)
      | (tcw,tcs,ts') :: tss ->
        if tcw = LB false then
          (* this is not even a weak embedding, so don't care *)
          step2 ge gt ss' tss
        else if tcs = LB false then
          (* this is at best \pi(t), so go real comparison *)
          let (ge2,gt2) = split (comparg_ac finfo order ss' ts') context in
          let (ge,gt) = (ge &^ (tcw =>^ ge2), gt |^ (tcw =>^ gt2)) in
          step2 ge gt ss' tss
        else
          let (ge3,gt3) = split (ac_rpo_compargs fname finfo ss' ts' order) context in
          let (ge,gt) =
            (ge &^ (tcw =>^ smt_if tcs gt3 ge3),
             gt |^ (tcw =>^ (smt_not tcs &^ gt3)))
          in
          step2 ge gt ss' tss
      in
      let rec step1 ge gt sss =
      match sss with
      | [] ->
        (ge,gt)
      | (scw,scs,ss') :: sss ->
        if scw = LB false then
          (* this is not even a weak embedding, so don't care *)
          step1 ge gt sss
        else if scs = LB false then
          (* this is at best only weak embedding, so go to the next step *)
          let (ge2,gt2) = step2 (LB true) (LB false) ss' tss in
          let (ge,gt) = (ge |^ (scw &^ ge2), gt |^ (scw &^ gt2)) in
          step1 ge gt sss
        else
          let (ge3,gt3) = split (ac_rpo_compargs fname finfo ss' ts order) context in
          (* if this is strict embedding, weak order results strict order *)
          step1 (ge |^ (scw &^ ge3)) (gt |^ (scw &^ smt_if scs ge3 gt3)) sss
      in
      let (ge,gt) = step1 (LB false) (LB false) sss in

      Cons(ge,gt);
    )
  in
  let ac_unmark_name name =
    if marked_name name then unmark_name name else name
  in
  let flat_compargs =
    if not p.dp && p.adm then
      fun fname gname finfo order ss ts ->
        if ac_unmark_name fname = ac_unmark_name gname then
          comparg_ac finfo order ss ts
        else
          not_ordered
    else
      fun fname gname finfo order ss ts ->
        let fname = ac_unmark_name fname in
        let gname = ac_unmark_name gname in
        if fname = gname then
          ac_rpo_compargs fname finfo ss ts order
        else not_ordered
  in
  (* compargs for f and g *)
  let compargs fname gname finfo ginfo =
    match finfo#base#ty, ginfo#base#ty with
    | Fun, Fun -> default_compargs finfo ginfo
    | Th "C", Th "C" -> fun order ss ts ->
      smt_if (finfo#mapped 1)
        (smt_if (ginfo#mapped 1) (mset_extension order ss ts) strictly_ordered)
        (smt_if (ginfo#mapped 1) weakly_ordered not_ordered)
    | Th "A", Th "A"
    | Th "AC", Th "AC"  -> fun order ss ts ->
      smt_if (finfo#mapped 1)
        (smt_if (ginfo#mapped 1)
          (flat_compargs fname gname finfo order ss ts)
          strictly_ordered
        )
        (smt_if (ginfo#mapped 1) weakly_ordered not_ordered)
    | _ -> fun _ _ _ -> not_ordered
  in

(*** RPO-like recursive checks ***)

  let order_by_some_arg =
    (* returns:
      some_ge <=> $s_i \gsim t$ for some $i \in \sigma(f)$
      some_gt <=> $s_i \gt t$ for some $i \in \sigma(f)$
    *)
    let rec sub i some_ge some_gt order finfo ss t =
      match ss with
      | []  -> Cons(some_ge, some_gt)
      | s::ss ->
        smt_split (order s t)
        (fun curr_ge curr_gt ->
          sub (i+1) 
          (some_ge |^ (finfo#permed i &^ curr_ge))
          (some_gt |^ (finfo#permed i &^ curr_gt)) order finfo ss t
        )
    in
    if p.Params.status_mode = S_empty then
      fun _ _ _ _ -> Cons(LB false, LB false)
    else if not p.collapse && p.adm then
      fun _ _ _ (WT(g,_,_)) -> let b = g#is_var in Cons(LB b, LB b)
    else if not p.collapse && p.mcw_val > 0 then
      fun order finfo ss t ->
        match ss with
        | [s] -> order s t
        | _ ->
          if finfo#max then
            sub 1 (LB false) (LB false) order finfo ss t
          else
            Cons(LB false, LB false)
    else
      sub 1 (LB false) (LB false)
  in
  let order_all_args =
    (* returns:
      all_ge <=> $s \gsim t_j$ for all $j \in \sigma(g)$
      all_gt <=> $s \gt t_j$ for all $j \in \sigma(g)$
    *)
    let rec sub j all_ge all_gt order s ginfo ts =
      match ts with
      | []  -> Cons(all_ge, all_gt)
      | t::ts ->
        smt_split (order s t)
        (fun curr_ge curr_gt ->
          smt_let Bool curr_gt
          (fun curr_gt ->
            sub (j+1)
            (all_ge &^ (ginfo#permed j =>^ curr_ge))
            (all_gt &^ (ginfo#permed j =>^ curr_gt)) order s ginfo ts
          )
        )
    in
    if p.Params.status_mode = S_empty then
      fun _ _ _ _ -> Cons(LB true, LB true)
    else if not p.collapse && p.adm then
      fun _ _ _ _ -> Cons(LB true, LB true)
    else if not p.collapse && p.mcw_val > 0 then
      fun order s ginfo ts ->
        match ts with
        | [t] -> order s t
        | _ ->
          if ginfo#max then
            sub 1 (LB true) (LB true) order s ginfo ts
          else
            Cons(LB true, LB true)
    else
      sub 1 (LB true) (LB true)
  in

(*** WPO frame ***)
  let is_mincons =
    if p.mincons then
      fun finfo -> finfo#is_quasi_const &^ (finfo#prec =^ pmin)
    else
      fun _ -> LB false
  in
  let is_maxcons =
    if p.maxcons then
      fun finfo -> maxcons &^ finfo#is_quasi_const &^ (finfo#prec =^ !pmax)
    else
      fun _ -> LB false
  in
  let rec var_eq xname (WT(g,ts,_)) =
    if g#is_var then
      LB(xname = g#name)
    else 
      let ginfo = lookup g in
      let rec sub j =
        function
        | [] -> LB true
        | t::ts -> (ginfo#argfilt j =>^ var_eq xname t) &^ sub (j+1) ts
      in
      is_mincons ginfo |^ (ginfo#collapse &^ Delay(fun _ -> sub 1 ts))
  in
  let rec wpo (WT(f,ss,sw) as s) (WT(g,ts,tw) as t) =
    if ac_eq s t then
      weakly_ordered
    else
      compose (wo sw tw) (wpo2 s t)
  and wpo2 (WT(f,ss,_) as s) (WT(g,ts,_) as t) =
    if f#is_var then
      Cons(var_eq f#name t, LB false)
    else
      if f#equals g then
        match ss,ts with
        | [s1], [t1] ->
          let fltp = (lookup f)#permed 1 in
          smt_split (wpo2 s1 t1) (fun rge rgt -> Cons(fltp =>^ rge, fltp &^ rgt))
        | _ -> wpo3 s t
      else wpo3 s t
  and wpo3 (WT(f,ss,_) as s) (WT(g,ts,_) as t) =
    let finfo = lookup f in
    smt_split (order_by_some_arg wpo finfo ss t)
    (fun some_ge some_gt ->
      smt_let Bool some_ge
      (fun some_ge ->
        let col_f = finfo#collapse in
        let some_gt = smt_if col_f some_gt some_ge in
        if some_gt = LB true then
          strictly_ordered
        else if g#is_var then
          Cons(some_ge |^ is_maxcons finfo, some_gt)
        else
          let ginfo = lookup g in
          smt_split (order_all_args wpo s ginfo ts)
          (fun all_ge all_gt ->
            let col_g = ginfo#collapse in
            if all_gt = LB false then
              Cons(some_ge |^ (col_g &^ all_ge), some_gt)
            else
              smt_split (compose (po s t) (compargs f#name g#name finfo ginfo wpo ss ts))
              (fun rest_ge rest_gt ->
                smt_let Bool all_gt
                (fun all_gt ->
                  let cond = smt_not col_f &^ smt_not col_g &^ all_gt in 
                  let ge = some_ge |^ (col_g &^ all_ge) |^ (cond &^ rest_ge) in
                  let gt = some_gt |^ (col_g &^ all_gt) |^ (cond &^ rest_gt) in
                  Cons(ge,gt)
                )
              )
          )
      )
    )
  in
  let frame =
    if p.prec_mode = PREC_none && p.status_mode = S_empty then
      fun (WT(_,_,sw)) (WT(_,_,tw)) -> wo sw tw
    else wpo
  in

object (x)

  inherit Wpo_printer.t p solver sigma mcw

  val mutable initialized = false
  val mutable use_scope = p.use_scope
  val mutable use_scope_last_size = 0
  val mutable dp_flag_table = Hashtbl.create 256
  val mutable rule_flag_table = Hashtbl.create 256
  val mutable prule_flag_table = Hashtbl.create 4

  method using_usable = if p.dp then p.usable else p.remove_all

  method init current_usables dps =
    initialized <- true;
    debug (puts " Initializing.");

    if p.use_scope_ratio > 0 then begin
      let rules_size = List.length current_usables in
      use_scope_last_size <- trs#get_size;
      use_scope <-
        (use_scope_last_size - rules_size) * p.use_scope_ratio < rules_size;
    end;
    if use_scope then begin
      debug(puts " `Scope' mode.");
      dplist := dg#get_dps;
      usables := trs#fold_rules (fun i rule rest -> (i,rule)::rest) [];
    end else begin
      dplist := List.fold_right (fun i acc -> (i, dg#find_dp i) :: acc) dps [];
      usables := List.map (fun i -> (i, trs#find_rule i)) current_usables;
    end;

    (* generating the signature *)
    Hashtbl.clear sigma;
    let iterer f =
      Hashtbl.add sigma f#name (new wpo_sym f);
    in
    trs#iter_funs iterer;

    (* count nesting *)
    if p.max_nest > 0 || p.status_nest > 0 || p.max_poly_nest > 0 then begin
      let rec nest_term (Node(f,ss)) =
        if f#is_var then
          Mset.empty
        else
          Mset.union (Mset.singleton f#name)
            (List.fold_left Mset.join Mset.empty (List.map nest_term ss))
      in
      let nest_rule rule = Mset.join (nest_term rule#l) (nest_term rule#r) in
      let nest_rules =
        fun rules ->
          List.fold_left Mset.join Mset.empty
            (List.map (fun (_,rule) -> nest_rule rule) rules)
      in
      nest_map := Mset.join (nest_rules !usables) (nest_rules !dplist)
    end;

    if p.prec_mode <> PREC_none then
      (* set max precedence *)
      pmax := LI (Hashtbl.length sigma);

    (* choice of max_status *)
    let set_max =
      let set_max_finfo fname finfo =
        not finfo#max &&
        finfo#base#arity > 1 &&
        (p.max_nest = 0 || nest fname <= p.max_nest) &&
        (
          debug2 (putc ' ' << put_name fname);
          finfo#set_max true;
          true
        )
      in
      function
      | MAX_dup ->
        let rec annote_vs (Node(f,ss)) =
          let args = List.map annote_vs ss in
          let argvss = List.map get_weight args in
          let vs =
            if f#is_var then [Mset.singleton f#name]
            else if (lookup f)#max then
              List.concat argvss
            else
              List.map (List.fold_left Mset.union Mset.empty) (list_product argvss)
          in
          WT(f,args,vs)
        in
        let vcond svss tvss =
          List.for_all (fun tvs -> List.exists (Mset.subseteq tvs) svss) tvss
        in
        let rec sub (WT(f,ss,svss) as s) (WT(g,ts,tvss)) =
          List.iter (sub s) ts;
          if  not (vcond svss tvss) &&
            set_max_finfo g#name (lookup g)
          then raise Continue;
        in
        let annote_sub (_,lr) =
          sub (annote_vs lr#l) (annote_vs lr#r);
        in
        let rec loop rulelist =
          try List.iter annote_sub rulelist with Continue -> loop rulelist
        in
        loop
      | MAX_all ->
        fun _ ->
          Hashtbl.iter (fun fname finfo -> ignore (set_max_finfo fname finfo)) sigma;
      | _ ->
        fun _ -> ();
    in

    debug2 (endl << puts "Max symbols: {");
    set_max p.max_mode !usables;
    set_max p.max_mode !dplist;
    debug2 (puts " }" << endl);

    solver#set_logic
    ( "QF_" ^
      (if p.sc_mode = W_num then "N" else "L") ^
      (if weight_ty = Real then "R" else "I") ^
      "A"
    );

    begin
      match p.mcw_mode with
      | MCW_num  -> solver#add_variable mcw_v weight_ty;
      | MCW_bool -> solver#add_variable mcw_v Bool;
      | _ -> ();
    end;
    solver#add_assertion (mcw >=^ mcw_val);

    if p.maxcons then
      solver#add_variable maxcons_v Bool;

    Hashtbl.iter add_symbol sigma;

    if p.prec_mode = PREC_strict then begin
      (* asserting no equivalence in precedence *)
      let rec subsub pf =
        function
        | [] -> ()
        | pg::pgs ->
          solver#add_assertion (smt_not (pf =^ pg));
          subsub pf pgs;
      in
      let rec sub =
        function
        | []    -> ()
        | pf::pfs -> subsub pf pfs; sub pfs
      in
      sub (Hashtbl.fold (fun _ finfo vs -> finfo#prec :: vs) sigma [])
    end;

    if p.prec_mode <> PREC_none then begin
      (* special treatment of associative symbols *)
      let iterer fname finfo =
        if finfo#base#is_associative then begin
          (* marked associative symbols have the precedence of unmarked one *)
          if marked_name fname then begin
            finfo#set_prec (lookup_name (unmark_name fname))#prec;
          end;
        end;
      in
      Hashtbl.iter iterer sigma;
    end;
    List.iter (fun (i,_) -> add_usable i) !usables;
    trs#iter_prules (fun i _ -> add_usable_p i);

  method private add_prule i =
    if not (Hashtbl.mem prule_flag_table i) then
    try
      Hashtbl.add prule_flag_table i ();
      let prule = trs#find_prule i in
      debug2 (puts "  Initializing probabilistic rule " << put_int i << endl);
      match get_weight (annote prule#l) with
      | [(vc,e)] ->
        let coef = LI(prule#sum) in
        let vc = Hashtbl.copy vc in
        vc_mul vc coef;
        let lw = (vc, coef *^ e) in
        let folder (vc,e) coef r =
          match get_weight (annote r) with
          | [(vc',e')] -> vc_mul_add vc (LI coef) vc'; (vc, e +^ (LI coef *^ e'))
          | _ -> raise (Internal "unsupported weight for probabilistic rule")
        in
        let rw = prule#fold_rs folder (Hashtbl.create 4, LI 0) in
        let (ge,gt) = split (polo lw rw) solver in
        solver#add_assertion (usable_p i =>^ ge);
        solver#add_definition (gt_p_v i) Bool gt;
      | _ -> raise (Internal "unsupported weight for probabilistic rule")
    with Inconsistent ->
      debug (puts " inconsistency detected." << endl);

  method private add_rule i =
    if not (Hashtbl.mem rule_flag_table i) then
    try
      Hashtbl.add rule_flag_table i ();
      let rule = trs#find_rule i in
      debug2 (puts "  Initializing rule " << put_int i << endl);
      let (WT(_,_,lw) as la) = annote rule#l in
      let (WT(_,_,rw) as ra) = annote rule#r in
      if p.dp then begin
        if p.usable_w then begin
          solver#add_assertion
            (usable_w i =>^ set_usable (fun finfo -> finfo#argfilt) usable_w rule#r);
          solver#add_assertion
            (usable i =>^ set_usable (fun finfo -> finfo#permed) usable rule#r);
          let wge, wgt = split (wo lw rw) solver in
          let wge = solver#refer Bool wge in
          solver#add_assertion (usable_w i =>^ wge);
          if wge = LB false then begin
            solver#add_definition (ge_r_v i) Bool (LB false);
            solver#add_definition (gt_r_v i) Bool (LB false);
          end else begin
            let (rge,rgt) = split (wpo2 la ra) solver in
            solver#add_definition (ge_r_v i) Bool (wge &^ rge);
            solver#add_definition (gt_r_v i) Bool (wgt |^ (wge &^ rgt));
          end;
        end else if p.usable then begin
          solver#add_assertion
            (usable i =>^ set_usable (fun finfo -> finfo#argfilt) usable rule#r);
          solver#add_assertion 
            (usable i =>^ weakly (frame la ra));
        end else begin
          solver#add_assertion (weakly (frame la ra));
        end;
      end else if p.remove_all then begin
        solver#add_assertion (strictly (frame la ra));
      end else begin
        (* rule removal mode *)
        let (ge,gt) = split (frame la ra) solver in
        solver#add_assertion (usable i =>^ ge);
        solver#add_definition (gt_r_v i) Bool gt;
      end;
    with Inconsistent ->
      debug (puts " inconsistency detected." << endl);

  method private add_dp i =
    if not (Hashtbl.mem dp_flag_table i) then begin
      Hashtbl.add dp_flag_table i ();
      debug2 (puts "    initializing DP #" << put_int i << endl);
      let dp = dg#find_dp i in
      let (ge,gt) = split (frame (annote dp#l) (annote dp#r)) solver in
      solver#add_definition (ge_v i) Bool ge;
      solver#add_definition (gt_v i) Bool gt;
      (* flag usable rules *)
      if p.usable_w then begin
        solver#add_assertion (set_usable (fun finfo -> finfo#argfilt) usable_w dp#r);
        solver#add_assertion (set_usable (fun finfo -> finfo#permed) usable dp#r);
      end else begin
        solver#add_assertion (set_usable (fun finfo -> finfo#argfilt) usable dp#r);
      end;
    end;

  method reset =
    begin
      match p.reset_mode with
      | RESET_reset -> solver#reset;
      | RESET_reboot -> solver#reboot;
    end;
    Hashtbl.clear dp_flag_table;
    Hashtbl.clear rule_flag_table;
    initialized <- false;

  method push current_usables dps =
    if initialized then begin
      if p.use_scope_ratio > 0 then
        let curr_size = trs#get_size in
        if (use_scope_last_size - curr_size) * p.use_scope_ratio > curr_size then
        begin
          x#reset;
          x#init current_usables dps;
        end;
    end else begin
      x#init current_usables dps;
    end;
    List.iter x#add_rule current_usables;
    List.iter x#add_dp dps;
    if use_scope then
      solver#push;

  method pop =
    if use_scope then
      solver#pop
    else
      x#reset;

  method reduce current_usables sccref =
    comment (puts (name_order p) << putc '.' << flush);
    try
      x#push current_usables !sccref;
      comment (putc '.' << flush);
      if p.remove_all then begin
        let iterer i =
          solver#add_assertion
          (EV (if (dg#find_dp i)#is_strict then gt_v i else ge_v i));
        in
        List.iter iterer !sccref;
      end else begin
        let folder i ret =
          solver#add_assertion (EV (ge_v i));
          EV (gt_v i) |^ ret
        in
        solver#add_assertion (List.fold_right folder !sccref (LB false));
      end;
      comment (putc '.' << flush);
      solver#check;
      comment (puts " succeeded." << endl);
      proof (x#output_proof << x#output_usables usable !usables);
      cpf (Xml.enter "acRedPairProc"); (* CAUTION: manually leave later *)
      cpf (x#output_cpf << Xml.enter "dps" << Xml.enter "rules");
      let folder i (cnt,rem_dps) =
        if solver#get_bool (EV(gt_v i)) then (
          cpf ((dg#find_dp i)#output_xml);
          dg#remove_dp i;
          sccref := list_remove ((=) i) !sccref;
          (cnt + 1, i :: rem_dps)
        ) else (cnt,rem_dps)
      in
      let (cnt,rem_dps) = List.fold_right folder !sccref (0,[]) in
      proof (puts "    Removed DPs:" << Abbrev.put_ints " #" rem_dps << endl);
      cpf (Xml.leave "rules" << Xml.leave "dps" << x#put_usables_cpf usable !usables);
      x#pop;
      cnt
    with Inconsistent ->
      comment (puts " ");
      x#pop;
      0

  method direct current_usables =
    try
      comment (puts "Direct " << puts (name_order p) << puts " ." << flush);
      x#push current_usables [];
      trs#iter_prules (fun i _ -> x#add_prule i);

      comment (putc '.' << flush);

      if not p.remove_all then begin
        (* usable i should be true until i is removed. *)
        List.iter (fun i -> solver#add_assertion (usable i)) current_usables;
        solver#add_assertion
          (smt_exists (fun i -> EV(gt_r_v i)) current_usables |^
           trs#fold_prules (fun i _ ret -> ret |^ EV(gt_p_v i)) (LB false)
          );
      end;
      comment (putc '.' << flush);
      solver#check;

      cpf (Xml.enter "acRuleRemoval"); (* CAUTION: enter but won't leave *)
      cpf x#output_cpf;
      cpf (Xml.enter "trs" << Xml.enter "rules");
      if p.remove_all then begin
        comment (puts " removes all." << endl);
        List.iter trs#remove_rule current_usables;
        trs#iter_prules (fun i _ -> trs#remove_prule i);
      end else begin
        comment (puts " removes:");
        List.iter
        (fun i ->
          if solver#get_bool (EV(gt_r_v i)) then begin
            cpf ((trs#find_rule i)#output_xml);
            trs#remove_rule i;
            comment(fun _ -> prerr_string " "; prerr_int i;);
          end;
        ) current_usables;
        trs#iter_prules
        (fun i _ ->
          if solver#get_bool (EV(gt_p_v i)) then begin
            trs#remove_prule i;
            comment(fun _ -> prerr_string " p"; prerr_int i;);
          end;
        );
        comment endl;
      end;
      proof x#output_proof;
      cpf (Xml.leave "rules" << Xml.leave "trs");
      x#pop;
      true
    with Inconsistent -> x#pop; false
end;;
