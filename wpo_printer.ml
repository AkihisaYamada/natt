open Util
open Sym
open Term
open Smt
open Params
open Io
open Wpo_info


(*** Printing proofs ***)

class t p (solver:#solver) sigma (interpreter:#Weight.interpreter) =
  let status_is_used =
    p.ext_mset && p.ext_lex ||
    p.Params.status_mode <> S_none && p.Params.status_mode <> S_empty ||
    p.collapse
  in
  let weight_is_used = p.w_mode <> W_none in
  let usable_is_used = p.dp && p.usable in
  let prec_is_used = p.prec_mode <> PREC_none in
  object
    method output_proof : 'pr. (#printer as 'pr) -> unit = fun pr ->
      let pr_exp e = put_exp e pr in
      let pr_perm finfo =
        pr#puts "s: ";
        let punct = ref "" in
        let rbr =
          if solver#get_bool finfo#collapse then ""
          else if solver#get_bool finfo#mset_status then
            (pr#puts "{"; "}")
          else (pr#puts "["; "]")
        in
        let n = finfo#base#arity in
        for j = 1 to n do
          for i = 1 to n do
            if solver#get_bool (finfo#perm i j) then begin
              pr#puts !punct;
              pr#put_int i;
              punct := ",";
            end;
          done;
        done;
        pr#puts rbr;
      in
      let pr_interpret finfo =
        interpreter#output_sym solver (pr:>#Io.printer) "\tw" finfo#base finfo#base#arity;
      in
      let pr_prec finfo =
        pr#puts "p: ";
        pr_exp (solver#get_value finfo#prec);
      in
      let pr_symbol fname (finfo:wpo_sym) =
        pr#puts "      ";
        finfo#base#output (pr:>Io.outputter);
        if status_is_used then begin
          pr#puts "\t";
          pr_perm finfo;
        end;
        if not (solver#get_bool finfo#collapse) then begin
          if prec_is_used then begin
            pr#puts "\t";
            pr_prec finfo;
          end;
          if weight_is_used then begin
            pr_interpret finfo;
          end;
        end;
        pr#endl;
      in
      Hashtbl.iter pr_symbol sigma;
    method output_usables : 'pr 'a. (int -> exp) -> (int * 'a) list -> (#printer as 'pr) -> unit =
      fun usable usables ->
      if usable_is_used || params.debug then
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
        Xml.enter "status" pr;
        let n = finfo#base#arity in
        for j = 1 to n do
          for i = 1 to n do
            if solver#get_bool (finfo#perm i j) then begin
              Xml.enclose_inline "position" (put_int i) pr;
            end;
          done;
        done;
        Xml.leave "status" pr;
      in
      let put_prec finfo =
        Xml.enclose "precedence" (put_int (smt_eval_int (solver#get_value finfo#prec)))
      in
      let pr_precstat pr _ (finfo:wpo_sym) =
        Xml.enclose "precedenceStatusEntry" (
          finfo#base#output_xml <<
          Xml.enclose_inline "arity" (put_int finfo#base#arity) <<
          put_prec finfo <<
          put_status finfo
        ) pr
      in
      let put_inte e =
        Xml.enclose_inline "coefficient" (Xml.enclose_inline "integer" (put_int (smt_eval_int e)))
      in
      let put_vec es =
        Xml.enclose "vector" (fun pr -> List.iter (fun e -> put_inte e pr) es)
      in
      let put_mat ess =
        Xml.enclose "matrix" (fun pr -> List.iter (fun es -> put_vec es pr) (Matrix.trans ess))
      in
      let put_coef e =
        Xml.enclose "polynomial" (
          match e with
          | Vec es -> Xml.enclose "coefficient" (put_vec es)
          | Mat ess -> Xml.enclose "coefficient" (put_mat ess)
          | _ -> put_inte e
        )
      in
      let pr_interpret pr _ (finfo:wpo_sym) =
        Xml.enter "interpret" pr;
(*
        finfo#base#output_xml pr;
        let n = finfo#base#arity in
        Xml.enclose_inline "arity" (put_int n) pr;
        let sc =
          if finfo#base#ty = Fun then finfo#subterm_coef
          else k_comb (finfo#subterm_coef 1)
        in
        let put_sum pr =
          Xml.enter "polynomial" pr;
          Xml.enter "sum" pr;
          for i = 1 to n do
            let coef = solver#get_value (sc i) in
            if is_zero coef then begin
              (* nothing *)
            end else if is_one coef then begin
              Xml.enclose "polynomial" (
                Xml.enclose_inline "variable" (
                  put_int i
                )
              ) pr;
            end else begin
              Xml.enclose "polynomial" (
                Xml.enclose "product" (
                  put_coef coef <<
                  Xml.enclose "polynomial" (
                    Xml.enclose_inline "variable" (
                      put_int i
                    )
                  )
                )
              ) pr;
            end;
          done;
          put_coef (solver#get_value finfo#weight) pr;
          Xml.leave "sum" pr;
          Xml.leave "polynomial" pr;
        in
        if finfo#max then begin
          let usemax = not (solver#get_bool finfo#collapse) in
          if usemax then begin
            Xml.enter "polynomial" pr;
            Xml.enter "max" pr;
          end;
          for i = 1 to n do
            let pen = solver#get_value (finfo#subterm_penalty i) in
            if solver#get_bool (finfo#maxfilt i) then begin
              Xml.enclose "polynomial" (
                Xml.enclose "sum" (
                  Xml.enclose "polynomial" (
                    Xml.enclose_inline "variable" (put_int i)
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
            Xml.leave "max" pr;
            Xml.leave "polynomial" pr;
          end;
        end else if p.w_neg && not (solver#get_bool finfo#is_const) then begin
          Xml.enclose "polynomial" (
            Xml.enclose "max" (
              put_sum <<
              put_coef (solver#get_value mcw)
            )
          ) pr;
        end else begin
          put_sum pr;
        end;
*)
        Xml.leave "interpret" pr;
      in
      fun pr ->
        Xml.enter "orderingConstraintProof" pr;
        Xml.enter "redPair" pr;
        if prec_is_used || status_is_used then begin
          Xml.enter "weightedPathOrder" pr;
          Xml.enter "precedenceStatus" pr;
          Hashtbl.iter (pr_precstat pr) sigma;
          Xml.leave "precedenceStatus" pr;
        end;
        Xml.enter "interpretation" pr;
        Xml.enclose "type" (
          if p.w_dim > 1 then
            Xml.enclose "matrixInterpretation" (
              Xml.enclose_inline "domain" (Xml.tag "naturals") <<
              Xml.enclose_inline "dimension" (put_int p.w_dim) <<
              Xml.enclose_inline "strictDimension" (puts "1")
            )
          else
            Xml.enclose "polynomial" (
              Xml.enclose_inline "domain" (Xml.tag "naturals") <<
              Xml.enclose_inline "degree" (puts "1")
            )
        ) pr;
        Hashtbl.iter (pr_interpret pr) sigma;
        Xml.leave "interpretation" pr;
        if prec_is_used || status_is_used then begin
          Xml.leave "weightedPathOrder" pr;
        end;
        Xml.leave "redPair" pr;
        Xml.leave "orderingConstraintProof" pr;
    method put_usables_cpf : 'pr. (int -> exp) -> (int * rule) list -> (#printer as 'pr) -> unit =
      fun usable usables pr ->
        Xml.enclose "usableRules" (
          Xml.enclose "rules" (fun (pr:#printer) ->
            let iterer (i, (rule:rule)) =
              if solver#get_bool (usable i) then rule#output_xml pr;
            in
            List.iter iterer usables;
          )
        ) pr
  end

