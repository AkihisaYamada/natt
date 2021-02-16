open Util
open Strategy

let version = "1.8";


type estimator_mode =
| E_tcap
| E_sym_trans
type sort_mode =
| SORT_asc
| SORT_desc
| SORT_none
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


(* checks monotonicity *)
let nonmonotone p =
  p.dp ||
  p.collapse ||
  p.status_mode = S_partial ||
  p.status_mode = S_empty && p.prec_mode <> PREC_none

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

let set_strategy (pre,freezing,rest) =
  params.orders_removal <- Array.of_list pre;
  params.uncurry <- freezing;
  ( match rest with
    | Some(post,loop) ->
      params.orders_dp <- Array.of_list post;
      params.max_loop <- loop;
    | None -> ()
  )
in
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
let erro str = err ("unknown option: " ^ str ^ "!") in
let safe_atoi s arg = (try int_of_string s with _ -> erro arg) in
let default = ref true in
while !i < argc do
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
    | "-s", Some file ->
      set_strategy (Strategy.of_file file);
      default := false;
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
    if params.file <> "" then err ("too many input file: " ^ arg ^ "!");
    params.file <- arg;
  end;
  i := !i + 1;
done;
if !default then begin
  set_strategy (Strategy.of_file "default.xml")
end

let cpf =
  if params.cpf then
    let os = new Io.pretty_wrap_out params.cpf_to in
    fun proc -> proc os
  else fun _ -> ()
