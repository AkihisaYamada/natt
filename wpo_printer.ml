open Util
open Sym
open Term
open Smt
open Params
open Io
open Wpo_info


(*** Printing proofs ***)

class t p (solver:#solver) sigma (interpreter:#Weight.interpreter) =
  let dim = Array.length p.w_templates in
  let status_is_used =
    p.ext_mset && p.ext_lex ||
    p.Params.status_mode <> S_none && p.Params.status_mode <> S_empty ||
    p.collapse
  in
  let weight_is_used = dim <> 0 in
  let usable_is_used = p.dp && p.usable in
  let prec_is_used = p.prec_mode <> PREC_none in
  object
    method output_proof : 'pr. (#printer as 'pr) -> unit = fun pr ->
      let pr_exp e = put_exp e pr in
      let pr_perm finfo =
        if status_is_used then begin
        let n = finfo#base#arity in
        if n > 0 then (
        let punct = ref "" in
        let rbr =
          if solver#get_bool finfo#collapse then ""
          else if solver#get_bool finfo#mset_status then
            (pr#puts "{"; "}")
          else (pr#puts "["; "]")
        in
        for j = 1 to n do
          for i = 1 to n do
            if solver#get_bool (finfo#perm i j) then begin
              pr#puts !punct;
              pr#putc 'x';
              pr#put_int i;
              punct := ",";
            end;
          done;
        done;
        pr#puts rbr
        );
        end;
      in
      let pr_interpret finfo =
        if weight_is_used then begin
          pr#puts "\tw: ";
          interpreter#output_sym solver finfo#base pr;
        end
      in
      let pr_prec finfo =
        if prec_is_used then begin
          pr_exp (solver#get_value finfo#prec);
        end;
      in
      let pr_symbol fname (finfo:wpo_sym) =
        pr#puts "  ";
        finfo#base#output (pr:>Io.outputter);
        pr#putc '(';
        (put_list (fun i -> putc 'x' << put_int i) (putc ',') nop (int_list 1 finfo#base#arity)) pr;
        pr#puts ")\t";
        if not (solver#get_bool finfo#collapse) then begin
          pr_prec finfo;
        end;
        pr_perm finfo;
        pr_interpret finfo;
        pr#endl;
      in
      Hashtbl.iter pr_symbol sigma;
    method output_usables : 'pr 'a. (int -> exp) -> (int * 'a) list -> (#printer as 'pr) -> unit =
      fun usable usables ->
      if usable_is_used || verbosity.(6) then
        let folder is (i,_) =
          if solver#get_bool (usable i) then i::is else is
        in
        puts "    USABLE RULES: {" <<
        Abbrev.put_ints " " (List.fold_left folder [] usables) <<
        puts " }" <<
        endl
      else fun _ -> ()

    (* Print CPF proof *)
    method output_cpf : 'pr. (#printer as 'pr) -> unit =
      let put_status finfo pr =
        MyXML.enter "status" pr;
        let n = finfo#base#arity in
        for j = 1 to n do
          for i = 1 to n do
            if solver#get_bool (finfo#perm i j) then begin
              MyXML.enclose_inline "position" (put_int i) pr;
            end;
          done;
        done;
        MyXML.leave "status" pr;
      in
      let put_prec finfo =
        MyXML.enclose "precedence" (put_int (smt_eval_int (solver#get_value finfo#prec)))
      in
      let pr_precstat pr _ (finfo:wpo_sym) =
        MyXML.enclose "precedenceStatusEntry" (
          finfo#base#output_xml <<
          MyXML.enclose_inline "arity" (put_int finfo#base#arity) <<
          put_prec finfo <<
          put_status finfo
        ) pr
      in
      let put_inte e =
        MyXML.enclose_inline "coefficient" (MyXML.enclose_inline "integer" (put_int (smt_eval_int e)))
      in
      let put_vec es =
        MyXML.enclose "vector" (fun pr -> List.iter (fun e -> put_inte e pr) es)
      in
      let put_mat ess =
        MyXML.enclose "matrix" (fun pr -> List.iter (fun es -> put_vec es pr) (Matrix.trans ess))
      in
      let put_coef e =
        MyXML.enclose "polynomial" (put_inte e)
      in
      let pr_interpret pr _ (finfo:wpo_sym) =
        MyXML.enter "interpret" pr;
(*
        finfo#base#output_xml pr;
        let n = finfo#base#arity in
        MyXML.enclose_inline "arity" (put_int n) pr;
        let sc =
          if finfo#base#ty = Fun then finfo#subterm_coef
          else k_comb (finfo#subterm_coef 1)
        in
        let put_sum pr =
          MyXML.enter "polynomial" pr;
          MyXML.enter "sum" pr;
          for i = 1 to n do
            let coef = solver#get_value (sc i) in
            if is_zero coef then begin
              (* nothing *)
            end else if is_one coef then begin
              MyXML.enclose "polynomial" (
                MyXML.enclose_inline "variable" (
                  put_int i
                )
              ) pr;
            end else begin
              MyXML.enclose "polynomial" (
                MyXML.enclose "product" (
                  put_coef coef <<
                  MyXML.enclose "polynomial" (
                    MyXML.enclose_inline "variable" (
                      put_int i
                    )
                  )
                )
              ) pr;
            end;
          done;
          put_coef (solver#get_value finfo#weight) pr;
          MyXML.leave "sum" pr;
          MyXML.leave "polynomial" pr;
        in
        if finfo#max then begin
          let usemax = not (solver#get_bool finfo#collapse) in
          if usemax then begin
            MyXML.enter "polynomial" pr;
            MyXML.enter "max" pr;
          end;
          for i = 1 to n do
            let pen = solver#get_value (finfo#subterm_penalty i) in
            if solver#get_bool (finfo#maxfilt i) then begin
              MyXML.enclose "polynomial" (
                MyXML.enclose "sum" (
                  MyXML.enclose "polynomial" (
                    MyXML.enclose_inline "variable" (put_int i)
                  ) <<
                  put_coef pen
                )
              ) pr;
            end;
          done;
          if finfo#sum then begin
            put_sum pr;
          end;
          if usemax then begin
            MyXML.leave "max" pr;
            MyXML.leave "polynomial" pr;
          end;
        end else if p.w_neg && not (solver#get_bool finfo#is_const) then begin
          MyXML.enclose "polynomial" (
            MyXML.enclose "max" (
              put_sum <<
              put_coef (solver#get_value mcw)
            )
          ) pr;
        end else begin
          put_sum pr;
        end;
*)
        MyXML.leave "interpret" pr;
      in
      fun pr ->
        MyXML.enter "orderingConstraintProof" pr;
        MyXML.enter "redPair" pr;
        if prec_is_used || status_is_used then begin
          MyXML.enter "weightedPathOrder" pr;
          MyXML.enter "precedenceStatus" pr;
          Hashtbl.iter (pr_precstat pr) sigma;
          MyXML.leave "precedenceStatus" pr;
        end;
        MyXML.enter "interpretation" pr;
        MyXML.enclose "type" (
          if dim > 1 then
            MyXML.enclose "matrixInterpretation" (
              MyXML.enclose_inline "domain" (MyXML.tag "naturals") <<
              MyXML.enclose_inline "dimension" (put_int dim) <<
              MyXML.enclose_inline "strictDimension" (puts "1")
            )
          else
            MyXML.enclose "polynomial" (
              MyXML.enclose_inline "domain" (MyXML.tag "naturals") <<
              MyXML.enclose_inline "degree" (puts "1")
            )
        ) pr;
        Hashtbl.iter (pr_interpret pr) sigma;
        MyXML.leave "interpretation" pr;
        if prec_is_used || status_is_used then begin
          MyXML.leave "weightedPathOrder" pr;
        end;
        MyXML.leave "redPair" pr;
        MyXML.leave "orderingConstraintProof" pr;
    method put_usables_cpf : 'pr. (int -> exp) -> (int * rule) list -> (#printer as 'pr) -> unit =
      fun usable usables pr ->
        MyXML.enclose "usableRules" (
          MyXML.enclose "rules" (fun (pr:#printer) ->
            let iterer (i, (rule:rule)) =
              if solver#get_bool (usable i) then rule#output_xml pr;
            in
            List.iter iterer usables;
          )
        ) pr
  end

