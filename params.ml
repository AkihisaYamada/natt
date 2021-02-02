open Util
open WeightTemplate

let version = "1.8";

type prec_mode =
| PREC_none
| PREC_strict
| PREC_quasi
| PREC_partial
type estimator_mode =
| E_tcap
| E_sym_trans
type max_mode =
| MAX_none
| MAX_all
| MAX_dup
type w_mode =
| W_none
| W_num
| W_bool
| W_tri
| W_quad
| W_arc
type status_mode =
| S_none
| S_empty
| S_partial
| S_total
type mcw_mode = (* minimum weight for constants *)
| MCW_num (* integer variable *)
| MCW_bool (* 0 or 1 *)
| MCW_const of int (* constant *)
type sort_mode =
| SORT_asc
| SORT_desc
| SORT_none
type reset_mode =
| RESET_reboot
| RESET_reset
type acdp_mode =
| ACDP_new
| ACDP_union
type ac_mark_mode =
| AC_unmark
| AC_mark
| AC_guard
type rdp_mode = (* for relative DP *)
| RDP_naive
| RDP_move
type mode =
| MODE_order
| MODE_flat
| MODE_uncurry
| MODE_simple
| MODE_dup
| MODE_through
| MODE_higher_xml
| MODE_xml

type smt_tool = string * string list

type order_params = {
  mutable dp : bool;
  mutable w_templates : WeightTemplate.entry array;
  mutable base_ty : Smt.ty;
  mutable tmpvar : bool;
  mutable ext_mset : bool;
  mutable ext_lex : bool;
  mutable status_mode : status_mode;
  mutable status_copy : bool;
  mutable status_nest : int;
  mutable prec_mode : prec_mode;
  mutable mincons : bool;
  mutable maxcons : bool;
  mutable ac_w : bool;
  mutable strict_equal : bool;
  mutable collapse : bool;
  mutable usable : bool;
  mutable usable_w : bool;
  mutable reset_mode : reset_mode;
  mutable use_scope : bool;
  mutable use_scope_ratio : int;
  mutable remove_all : bool;
  mutable smt_tool : smt_tool;
  mutable peek_in : bool;
  mutable peek_out : bool;
  mutable peek_to : out_channel;
}

let z3cmd = ("z3", ["-smt2";"-in"])
let cvc4cmd = ("cvc4", ["--lang=smt2"; "--incremental";"--produce-models"])

(* checks monotonicity *)
let nonmonotone p =
  p.dp ||
  p.collapse ||
  p.status_mode = S_partial ||
  p.status_mode = S_empty && p.prec_mode <> PREC_none

let order_default = {
  dp = false;
  base_ty = Smt.Real;
  tmpvar = true;
  w_templates = Array.make 0 (WeightTemplate.Nat(WeightTemplate.Const 0));
  ext_lex = false;
  ext_mset = false;
  status_mode = S_total;
  status_nest = 0;
  status_copy = false;
  prec_mode = PREC_quasi;
  mincons = false;
  maxcons = false;
  ac_w = true;
  strict_equal = false;
  collapse = false;
  usable = true;
  usable_w = false;
  reset_mode = RESET_reset;
  use_scope = true;
  use_scope_ratio = 0;
  remove_all = false;
  smt_tool = z3cmd;
  peek_in = false;
  peek_out = false;
  peek_to = stderr;
}

let name_order p =
  let status =
    match p.status_mode with
    | S_partial -> "pS"
    | S_total -> "S"
    | S_empty -> "eS"
    | _ -> ""
  in
  let prec =
    if p.prec_mode = PREC_quasi then "Q" else ""
  in
  if Array.length p.w_templates = 0 then
    prec ^ (
      match p.ext_lex, p.ext_mset with
      | true, true -> "RPO" ^ status
      | true, false -> "LPO" ^ status
      | false, true -> "MPO"
      | _ -> "???"
    )
  else if p.status_mode = S_empty && p.prec_mode = PREC_none then
    "Interpretation"
  else
    prec ^ "WPO" ^ status

type params_type = {
  mutable mode : mode;
  mutable file : string;
  mutable dp : bool;
  mutable edge_mode : estimator_mode;
  mutable edge_length : int;
  mutable sort_scc : sort_mode;
  mutable uncurry : bool;
  mutable max_loop : int;
  mutable max_narrowing : int;
  mutable acdp_mode : acdp_mode;
  mutable rdp_mode : rdp_mode;
  mutable ac_mark_mode : ac_mark_mode;
  mutable orders_removal : order_params array;
  mutable orders_dp : order_params array;
  mutable result : bool;
  mutable cpf : bool;
  mutable cpf_to : out_channel;
  mutable relative_usable : bool;
  mutable naive_C : bool;
};;

let params = {
  mode = MODE_order;
  file = "";
  dp = false;
  edge_mode = E_sym_trans;
  edge_length = 8;
  sort_scc = SORT_asc;
  uncurry = false;
  max_loop = 0;
  max_narrowing = 8;
  acdp_mode = ACDP_new;
  rdp_mode = RDP_move;
  ac_mark_mode = AC_mark;
  orders_removal = Array.make 0 order_default;
  orders_dp = Array.make 0 order_default;
  result = true;
  cpf = false;
  cpf_to = stdout;
  relative_usable = true;
  naive_C = false;
};;

let err msg =
  prerr_endline msg;
  print_endline "ERR";
  exit 1;
in
let argv = Sys.argv in
let argc = Array.length argv in
let progdir = Filename.dirname argv.(0) in
let prerr_help () =
  let pr = prerr_string in
  let pe = prerr_endline in
  pr "NaTT ver."; pe version;
  pr "Usage: "; pr argv.(0); pe " [FILE] [OPTION]... [PROCESSOR]...";
  pe "";
  pe "Checks termination of TRS specified by FILE (stdin by default).";
  pe "";
  pe "Global OPTIONs:";
  pe "  -v:<n>           set verbosity (0 to 6, default: 3).";
  pe "  --smt \"CMD\"      calls \"CMD\" as the back-end SMT solver.";
  pe "  --peek[-in|-out] dump transactions with the SMT solver.";
  pe "";
  pe "PROCESSORs: <ORDER> [OPTION]... | UNCURRY | EDG | LOOP";
  pe "ORDERs: WPO | POLO | LPO | MPO | RPO";
  pe "";
  pe "Options for orders:";
  pe "  -u/-U        enable/disable usable rules (after EDG, enabled by default).";
  pe "  -w:<temp>    introduce a weight template.";
  pe "  -c[:<n>]     enable coefficients (with bound <n>). Requires QF_NIA solver.";
  pe "  -c:b         enable binary coefficients (default after EDG).";
  pe "  -C           disable coefficients.";
  pe "  -p[:s]/-P    enable/disable [strict] precedences.";
  pe "  -s:{t/p/e}   use total/partial/empty statuses";
  pe "  -S           disable statuses.";
  pe "  --mset       enable multiset status.";
in
let i = ref 1 in
let pp = ref order_default in
let register_order p =
  if params.dp then begin
    params.orders_dp <- Array.append params.orders_dp (Array.make 1 p);
    pp := params.orders_dp.(Array.length params.orders_dp - 1);
  end else begin
    params.orders_removal <- Array.append params.orders_removal (Array.make 1 p);
    pp := params.orders_removal.(Array.length params.orders_removal - 1);
  end;
in
let register_weights wts =
  (!pp).w_templates <- Array.append (!pp).w_templates (Array.of_list wts);
in
let apply_edg () =
  if params.dp then err "'EDG' cannot be applied twice!";
  params.dp <- true;
  order_default.dp <- true;
  order_default.collapse <- not params.cpf;
  order_default.status_mode <- S_partial;
  pp := order_default;
in
let apply_polo () =
  register_order {
    order_default with
    ext_lex = false;
    ext_mset = false;
    status_mode = S_empty;
    prec_mode = PREC_none;
    collapse = false;
    usable_w = false;
    base_ty = Smt.Real;
  };
in
let apply_wpo () =
  register_order {
    order_default with
    ext_lex = true;
  };
in
let apply_lpo () =
  register_order {
    order_default with
    status_mode = if params.dp then S_partial else S_total;
    ext_lex = true;
  };
in
let erro str = err ("unknown option: " ^ str ^ "!") in
let safe_atoi s arg = (try int_of_string s with _ -> erro arg) in
let default = ref true in
while !i < argc do
  let p = !pp in
  let arg = argv.(!i) in
  if arg.[0] = '-' then begin
    let (opt,optarg) =
      let len = String.length arg in
      try let b = String.index argv.(!i) ':' in
        (String.sub arg 1 (b - 1), Some(String.sub arg (b+1) (len - b - 1)))
      with Not_found ->
        (String.sub arg 1 (len - 1), None)
    in
    match opt, optarg with
    | "-help", _ -> prerr_help (); exit 0;
    | "-all", None -> p.remove_all <- true;
    | "-Tempvar", None -> p.tmpvar <- false;
    | "-Sort", None -> params.sort_scc <- SORT_none;
    | "-sort", _ -> (
      match optarg with
      | None -> params.sort_scc <- SORT_asc;
      | Some "desc" -> params.sort_scc <- SORT_desc;
      | _ -> erro arg;
    )
    | "-naive-C", None -> params.naive_C <- true;
    | "-ac", Some s -> (
        match s with
        | "new" -> params.acdp_mode <- ACDP_new;
        | "union" -> params.acdp_mode <- ACDP_union;
        | "u" -> params.ac_mark_mode <- AC_unmark;
        | "m" -> params.ac_mark_mode <- AC_mark;
        | "g" -> params.ac_mark_mode <- AC_guard;
        | _ -> erro arg;
    )
    | "-rdp", Some s -> (
      match s with
      | "naive" -> params.rdp_mode <- RDP_naive;
      | _ -> erro arg;
    )
    | "v", Some s -> (
      match s with
      | "p" | "problem" -> verbosity.(3) <- true;
      | "l" | "log" -> verbosity.(4) <- true;
      | "d" | "debug" -> verbosity.(5) <- true;
      | "d2" | "debug2" -> verbosity.(6) <- true;
      | _ ->
        let v = safe_atoi s arg in
        for i = 0 to Array.length verbosity - 1 do
          verbosity.(i) <- v > i;
        done
    )
    | "V", None ->
      for i = 0 to Array.length verbosity - 1 do
        verbosity.(i) <- false;
      done
    | "x", None ->
      for i = 0 to Array.length verbosity - 1 do
        verbosity.(i) <- false;
      done;
      params.result <- false;
      params.cpf <- true;
      params.naive_C <- true;
      params.sort_scc <- SORT_none; (* for CeTA, the order is crusial *)
    | "x", Some file ->
      params.cpf <- true;
      params.cpf_to <- open_out file;
      params.naive_C <- true;
      params.sort_scc <- SORT_none; (* for CeTA, the order is crusial *)
    | "-peek", _ -> (
        p.peek_in <- true;
        p.peek_out <- true;
        match optarg with
        | Some file -> p.peek_to <- open_out file;
        | _ -> ();
    )
    | "-peek-in", None -> p.peek_in <- true;
    | "-peek-out", _ -> (
      p.peek_out <- true;
      match optarg with
      | Some file -> p.peek_to <- open_out file;
      | _ -> ();
    )
    | "f", None -> p.collapse <- true;
    | "F", None -> p.collapse <- false;
    | "u", None -> if not p.dp then err "-u cannot be applied here!"; p.usable <- true;
    | "U", None -> p.usable <- false;
    | "uw", None -> p.usable_w <- true;
    | "Uw", None -> p.usable_w <- false;
    | "ur", None -> params.relative_usable <- true;
    | "Ur", None -> params.relative_usable <- false;
    | "s", _ -> (
      match optarg with
      | Some "t" -> p.status_mode <- S_total;
      | Some "e" -> p.status_mode <- S_empty;
      | Some "p" -> p.status_mode <- S_partial;
      | None -> p.status_mode <- if p.dp then S_partial else S_total;
      | _ -> erro arg;
    )
    | "S", None -> p.status_mode <- S_none;
    | "-mset", None -> p.ext_mset <- true;
    | "-Lex", None -> p.ext_lex <- false;
    | "p", _ -> (
      match optarg with
      | Some "q" -> p.prec_mode <- PREC_quasi;
      | Some "s" -> p.prec_mode <- PREC_strict;
      | Some "p" -> p.prec_mode <- PREC_partial;
      | None -> p.prec_mode <- PREC_quasi;
      | _ -> erro arg;
    )
    | "P", None -> p.prec_mode <- PREC_none;
    | "w", Some str -> (
      default := false;
      register_weights (WeightTemplate.parse_file (progdir ^ "/" ^ str));
    )
    | "-min", None -> p.mincons <- true;
    | "-ty", Some "real" -> p.base_ty <- Smt.Real;
    | "-ty", Some "int" -> p.base_ty <- Smt.Int;
    | "n", _ ->
      begin
        match optarg with
        | Some s -> params.max_narrowing <- safe_atoi s arg;
        | None -> params.max_narrowing <- 7;
      end;
    | "-N", None -> params.max_narrowing <- 0;
    | "l", _ ->
      begin
        match optarg with
        | Some s -> params.max_loop <- safe_atoi s arg;
        | None -> params.max_loop <- 3;
      end;
    | "-L", None -> params.max_loop <- 0;

    | "-reset", _ ->
      begin
        match optarg with
        | None -> p.use_scope <- false; p.use_scope_ratio <- 0;
        | Some s -> p.use_scope <- false; p.use_scope_ratio <- safe_atoi s arg;
      end;
    | "-Reset", None -> p.use_scope <- true; p.use_scope_ratio <- 0;
    | "-reboot", None -> p.reset_mode <- RESET_reboot;
    | "-smt", _ -> (
      let cmd =
        match optarg with
        | None -> i := !i + 1; argv.(!i)
        | Some s -> s
      in
      match Str.split (Str.regexp "[ \t]+") cmd with
      | tool::options -> p.smt_tool <- (tool,options);
      | _ -> err "Please specify a valid SMT solver!";
    )
    | "-z3", None -> p.smt_tool <- z3cmd;
    | "-cvc4", None -> p.smt_tool <- cvc4cmd; p.reset_mode <- RESET_reboot;
    | "-dup", None -> default := false; params.mode <- MODE_dup;
    | "-tcap", None -> params.edge_mode <- E_tcap;
    | "-edge", Some s -> params.edge_length <- safe_atoi s arg;
    | "t", mode -> (
      default := false;
      match mode with
      | Some "ho" -> params.mode <- MODE_higher_xml;
      | Some "x" -> params.mode <- MODE_xml;
      | Some str -> err ("Unknown transformation mode: " ^ str ^ "!");
      | _ -> params.mode <- MODE_through;
    )
    | _ -> erro arg;
  end else begin
    match arg with
    | "UNCURRY" ->
      default := false;
      if params.dp then err "UNCURRY after EDG is not yet supported!";
      params.uncurry <- true;
    | "EDG" ->
      default := false;
      apply_edg ();
    | "LOOP" ->
      default := false;
      if not params.dp then err "LOOP cannot be applied before EDG!";
      params.max_loop <- 3;
    | "WPO" ->
      default := false;
      apply_wpo ();
    | "LPO" ->
      default := false;
      apply_lpo ();
    | "MPO" ->
      default := false;
      register_order {
        order_default with
        ext_lex = false;
        ext_mset = true;
        status_mode = if params.dp then S_partial else S_total;
      };
    | "RPO" ->
      default := false;
      register_order {
        order_default with
        ext_lex = true;
        ext_mset = true;
        status_mode = if params.dp then S_partial else S_total;
      };
    | "POLO" ->
      default := false;
      apply_polo ();
      register_weights (if params.dp then sum_template else mono_sum_template);
    | "O" ->
      default := false;
      apply_polo ();
    | "sum" ->
      default := false;
      register_weights (if params.dp then sum_template else mono_sum_template);
    | "max" ->
      default := false;
      register_weights (if params.dp then max_template else mono_max_template);
    | _ ->
      if params.file <> "" then err ("too many input file: " ^ arg ^ "!");
      params.file <- arg;
  end;
  i := !i + 1;
done;
if !default then begin
  (* the default strategy *)
  apply_polo ();
  register_weights mono_poly_template;
  params.uncurry <- not params.cpf; (* certifed uncurrying not supported *)
  apply_edg ();
  params.naive_C <- params.cpf;
  apply_polo ();
  register_weights sum_template;
  apply_polo ();
  register_weights max_template;
  apply_lpo ();
  apply_polo ();
  register_weights (neg_max_sum_template 4);
  apply_wpo ();
  register_weights (max_sum_template 4);
  !pp.status_mode <- S_partial;
  apply_polo ();
  register_weights (bmat_template 2);
  (* certified nontermination not supported *)
  if not params.cpf then params.max_loop <- 3;
end

let cpf =
  if params.cpf then
    let os = new Io.pretty_wrap_out params.cpf_to in
    fun proc -> proc os
  else fun _ -> ()
