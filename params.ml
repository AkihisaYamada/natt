let version = "1.2.-1";

type base_ty =
| TY_int
| TY_real
type prec_mode =
| PREC_none
| PREC_strict
| PREC_quasi
| PREC_partial
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
type status_mode =
| S_none
| S_empty
| S_partial
| S_total
type mcw_mode = (* minimum weight for constants *)
| MCW_num (* integer variable *)
| MCW_bool (* 0 or 1 *)
| MCW_const (* constant *)
type sort_mode =
| SORT_asc
| SORT_desc
| SORT_none
type reset_mode =
| RESET_reboot
| RESET_reset
type ac_mode = (* for AC; how AC arguments are compared first *)
| AC_rec (* recursive check *)
| AC_S90 (* Stenbach *)
| AC_KV03 (* Korovin & Voronkov *)
| AC_KV' (* $>_{W,top'}$ *)
| AC_weight (* weight $>_W$ *)
type acdp_mode =
| ACDP_KT98
| ACDP_MU98
| ACDP_GK01
| ACDP_new
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
| MODE_dp
| MODE_theory
| MODE_debug
| MODE_simple
| MODE_dist
| MODE_dup
| MODE_through
| MODE_higher_xml
| MODE_id
| MODE_relative_test
type smt_tool = string * string list

type order_params =
{
	mutable dp : bool;
	mutable w_mode : w_mode;
	mutable w_dim : int;
	mutable w_max : int;
	mutable w_neg : bool;
	mutable ext_mset : bool;
	mutable ext_lex : bool;
	mutable status_mode : status_mode;
	mutable status_copy : bool;
	mutable status_nest : int;
	mutable sc_mode : w_mode;
	mutable sc_max : int;
	mutable max_nest : int;
	mutable max_mode : max_mode;
	mutable max_poly_nest : int;
	mutable max_poly : bool;
	mutable sp_mode : w_mode;
	mutable prec_mode : prec_mode;
	mutable mcw_mode : mcw_mode;
	mutable mcw_val : int;
	mutable mincons : bool;
	mutable maxcons : bool;
	mutable adm : bool;
	mutable ac_mode : ac_mode;
	mutable ac_w : bool;
	mutable strict_equal : bool;
	mutable base_ty : base_ty;
	mutable collapse : bool;
	mutable usable : bool;
	mutable usable_w : bool;
	mutable refer_w : bool;
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
	p.w_neg ||
	p.collapse ||
	p.status_mode = S_partial ||
	p.status_mode = S_empty && (p.max_mode <> MAX_none || p.prec_mode <> PREC_none)

let order_default =
{
	dp = false;
	base_ty = TY_int;
	w_mode = W_none;
	w_dim = 1;
	w_max = 0;
	w_neg = false;
	ext_lex = false;
	ext_mset = false;
	status_mode = S_total;
	status_nest = 0;
	status_copy = false;
	sc_mode = W_none;
	sc_max = 0;
	max_nest = 0;
	max_mode = MAX_none;
	max_poly = false;
	max_poly_nest = 0;
	sp_mode = W_num;
	prec_mode = PREC_quasi;
	mcw_mode = MCW_const;
	mcw_val = 0;
	mincons = false;
	maxcons = false;
	adm = false;
	ac_mode = AC_rec;
	ac_w = true;
	strict_equal = false;
	collapse = false;
	usable = false;
	usable_w = false;
	refer_w = true;
	reset_mode = RESET_reset;
	use_scope = true;
	use_scope_ratio = 3;
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
	let base =
		if p.w_dim > 1 then
			"Mat" ^ string_of_int p.w_dim ^
			match p.sc_mode with
			| W_none -> "?"
			| W_num  -> ""
			| W_bool -> "b"
			| W_tri  -> "t"
			| W_quad  -> "q"
		else
			match p.sc_mode with
			| W_none -> "Sum"
			| W_num  -> "Pol"
			| W_bool -> if p.dp then "Sum" else "bPol"
			| W_tri  -> "tPol"
			| W_quad  -> "qPol"
	in
	let algebra =
		match p.max_mode with
		| MAX_none -> base
		| MAX_all -> if p.max_poly then "Max" ^ base else "max"
		| MAX_dup -> (if p.max_poly then "M" else "m") ^ base
	in
	if p.w_mode = W_none then
		prec ^ (
			match p.ext_lex, p.ext_mset with
			| true, true -> "RPO" ^ status
			| true, false -> "LPO" ^ status
			| false, true -> "MPO"
			| _ -> "???"
		)
	else if p.status_mode = S_empty && p.prec_mode = PREC_none then
		if p.w_dim > 1 then
			algebra
		else
			"POLO(" ^ algebra ^ ")"
	else if p.adm then
		if p.mcw_val = 0 || p.max_mode <> MAX_none then
			prec ^ "GKBO" ^ status ^ "(" ^ algebra ^ ")"
		else if p.sc_mode = W_none || p.sc_mode = W_bool && p.dp then
			match p.ac_mode with
			| AC_KV03 -> "KV03"
			| AC_KV' -> "KV03i"
			| AC_S90 -> "S90" ^ if p.ac_w then "i" else ""
			| _ -> prec ^ "KBO" ^ status
		else
			prec ^ "TKBO" ^ (
				match p.sc_mode with
				| W_quad -> "q"
				| W_bool -> "b"
				| _ -> ""
			) ^ status
	else
		prec ^ "WPO" ^ status ^ "(" ^ algebra ^ ")"

type params_type =
{
	mutable mode : mode;
	mutable file : string;
	mutable sort_scc : sort_mode;
	mutable uncurry : bool;
	mutable max_loop : int;
	mutable max_narrowing : int;
	mutable acdp_mode : acdp_mode;
	mutable rdp_mode : rdp_mode;
	mutable ac_mark_mode : ac_mark_mode;
	mutable orders_removal : order_params array;
	mutable orders_dp : order_params array;
	mutable warning : bool;
	mutable comment : bool;
	mutable problem : bool;
	mutable cpf : bool;
	mutable proof : bool;
	mutable debug : bool;
	mutable debug2 : bool;
	mutable tmpvar : bool;
	mutable relative_usable : bool;
};;

let params =
{
	mode = MODE_order;
	file = "";
	sort_scc = SORT_asc;
	uncurry = false;
	max_loop = 0;
	max_narrowing = 8;
	acdp_mode = ACDP_new;
	rdp_mode = RDP_move;
	ac_mark_mode = AC_unmark;
	orders_removal = Array.make 0 order_default;
	orders_dp = Array.make 0 order_default;
	warning = true;
	comment = true;
	problem = true;
	cpf = false;
	proof = true;
	debug = false;
	debug2 = false;
	tmpvar = true;
	relative_usable = true;
};;

let dp = ref false in
let err msg =
	prerr_endline msg;
	print_endline "ERR";
	exit 1;
in
let argv = Sys.argv in
let argc = Array.length argv in
let prerr_help () =
	let pr = prerr_string in
	let pe = prerr_endline in
	pr "NaTT ver."; pe version;
	pr "Usage: "; pr argv.(0); pe " [FILE] [OPTION]... [PROCESSOR]...";
	pe "";
	pe "Checks termination of TRS specified by FILE (stdin by default).";
	pe "";
	pe "Global OPTIONs:";
	pe "  -v:<n>           set verbosity (0 to 5, default: 3).";
	pe "  --smt \"CMD\"      calls \"CMD\" as the back-end SMT solver.";
	pe "  --peek[-in|-out] dump transactions with the SMT solver.";
	pe "";
	pe "PROCESSORs: <ORDER> [OPTION]... | UNCURRY | EDG | LOOP";
	pe "ORDERs: WPO | POLO | LPO | MPO | RPO | KBO";
	pe "";
	pe "Options for orders:";
	pe "  -u/-U        enable/disable usable rules (after EDG, enabled by default).";
	pe "  -w[:<n>]/-W  enable/disable weights (with bound <n>).";
	pe "  -w:neg       enable negative constants (after EDG).";
	pe "  -c[:<n>]     enable coefficients (with bound <n>). Requires QF_NIA solver.";
	pe "  -c:b         enable binary coefficients (default after EDG).";
	pe "  -C           disable coefficients.";
	pe "  --dim:<n>    matrix interpretations of dimension <n>.";
	pe "  -a:<alg>     specify a template algebra in {pol,max,mpol}.";
	pe "  -p[:s]/-P    enable/disable [strict] precedences.";
	pe "  -s:{t/p/e}   use total/partial/empty statuses";
	pe "  -S           disable statuses.";
	pe "  --mset       enable multiset status.";
in
let i = ref 1 in
let pp = ref order_default in
let register_order p =
	if !dp then begin
		params.orders_dp <- Array.append params.orders_dp (Array.make 1 p);
		pp := params.orders_dp.(Array.length params.orders_dp - 1);
	end else begin
		params.orders_removal <- Array.append params.orders_removal (Array.make 1 p);
		pp := params.orders_removal.(Array.length params.orders_removal - 1);
	end;
in
let apply_edg () =
	dp := true;
	order_default.dp <- true;
	order_default.usable <- true;
	order_default.sc_mode <- W_bool;
	order_default.collapse <- true;
	order_default.status_mode <- S_partial;
	pp := order_default;
in
let apply_polo () =
	register_order
	{
		order_default with
		ext_lex = false;
		ext_mset = false;
		status_mode = S_empty;
		prec_mode = PREC_none;
		w_mode = W_num;
		collapse = false;
		usable_w = false;
		refer_w = false;
	};
in
let apply_lpo () =
	register_order
	{
		order_default with
		ext_lex = true;
		max_mode = MAX_all;
		sp_mode = W_none;
		status_mode = S_total;
	};
in
let apply_wpo () =
	register_order
	{
		order_default with
		ext_lex = true;
		w_mode = W_num;
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
		match opt,optarg with
		| "-help", _ ->
			prerr_help (); exit 0;
		| "-all", None ->
			if p.dp then err "--all cannot applied here!";
			p.remove_all <- true;
		| "-Tempvar",None ->
			params.tmpvar <- false;
		| "-Sort", None -> params.sort_scc <- SORT_none;
		| "-sort", _ ->
			begin
				match optarg with
				| None -> params.sort_scc <- SORT_asc;
				| Some "desc" -> params.sort_scc <- SORT_desc;
				| _ -> erro arg;
			end
		| "-ac", Some s ->
			begin
				match s with
				| "MU98" -> params.acdp_mode <- ACDP_MU98;
				| "KT98" -> params.acdp_mode <- ACDP_KT98;
				| "GK01" -> params.acdp_mode <- ACDP_GK01;
				| "u" -> params.ac_mark_mode <- AC_unmark;
				| "m" -> params.ac_mark_mode <- AC_mark;
				| "g" -> params.ac_mark_mode <- AC_guard;
				| "rec" -> p.ac_mode <- AC_rec;
				| "S90" -> p.ac_mode <- AC_S90; p.ac_w <- false;
				| "S90i" -> p.ac_mode <- AC_S90; p.ac_w <- true;
				| "KV03"-> p.ac_mode <- AC_KV03;
				| "KV03i"-> p.ac_mode <- AC_KV';
				| "w" -> p.ac_mode <- AC_weight;
				| _ -> erro arg;
			end;
		| "-rdp", Some s ->
			begin
				match s with
				| "naive" -> params.rdp_mode <- RDP_naive;
				| _ -> erro arg;
			end;
		| "V", None ->
			params.warning <- false;
			params.comment <- false;
			params.problem <- false;
			params.proof <- false;
		| "v", _ ->
			let v =
				match optarg with
				| Some s -> safe_atoi s arg
				| _ -> 3
			in
			params.comment <- v > 0;
			params.problem <- v > 1;
			params.proof <- v > 2;
			params.debug <- v > 3;
			params.debug2 <- v > 4;
		| "x", None ->
			params.warning <- false;
			params.comment <- false;
			params.problem <- false;
			params.proof <- false;
			params.cpf <- true;
		| "-peek", _ ->
			begin
				p.peek_in <- true;
				p.peek_out <- true;
				match optarg with
				| Some file -> p.peek_to <- open_out file;
				| _ -> ();
			end;
		| "-peek-in", None -> p.peek_in <- true;
		| "-peek-out", _ ->
			begin
				p.peek_out <- true;
				match optarg with
				| Some file -> p.peek_to <- open_out file;
				| _ -> ();
			end;
		| "a", Some s ->
			begin
				match s with
				| "pol" -> p.max_mode <- MAX_none;
				| "max" -> p.max_mode <- MAX_all; p.refer_w <- true;
				| "mpol" -> p.max_mode <- MAX_dup; p.refer_w <- true;
				| "mpol2" -> p.max_mode <- MAX_dup; p.max_poly <- true; p.refer_w <- true;
				| _ -> erro arg;
			end;

		| "m", Some s -> p.max_nest <- safe_atoi s arg;

		| "-dim", Some s ->
			p.w_dim <- safe_atoi s arg;
			if p.w_dim > 10 then err "too big dimension!";

		| "f", None -> p.collapse <- true;
		| "F", None -> p.collapse <- false;
		| "u", None -> if not p.dp then err "-u cannot be applied here!"; p.usable <- true;
		| "U", None -> p.usable <- false;
		| "uw", None -> p.usable_w <- true;
		| "Uw", None -> p.usable_w <- false;
		| "ur", None -> params.relative_usable <- true;
		| "Ur", None -> params.relative_usable <- false;

		| "s", _ ->
			begin
				match optarg with
				| Some "t" -> p.status_mode <- S_total;
				| Some "e" -> p.status_mode <- S_empty;
				| Some "p" -> p.status_mode <- S_partial;
				| None -> p.status_mode <- if p.dp then S_partial else S_total;
				| _ -> erro arg;
			end;
		| "S", None -> p.status_mode <- S_none;
		| "-mset", None -> p.ext_mset <- true;
		| "-Lex", None -> p.ext_lex <- false;

		| "p", _ ->
			begin
				match optarg with
				| Some "q" -> p.prec_mode <- PREC_quasi;
				| Some "s" -> p.prec_mode <- PREC_strict;
				| Some "p" -> p.prec_mode <- PREC_partial;
				| None -> p.prec_mode <- PREC_quasi;
				| _ -> erro arg;
			end;
		| "P", None -> p.prec_mode <- PREC_none;

		| "-adm", None -> p.adm <- true;
		| "-Adm", None -> p.adm <- false;

		| "r", None -> p.refer_w <- true;
		| "R", None -> p.refer_w <- false;

		| "w", _ ->
			begin
				match optarg with
				| Some "neg" -> p.w_mode <- W_num; p.w_neg <- true;
				| Some "b" -> p.w_mode <- W_bool;
				| Some s -> p.w_max <- safe_atoi s arg; p.w_mode <- W_num;
				| None -> p.w_mode <- W_num;
			end;
		| "W", None -> p.w_mode <- W_none;

		| "c", _ ->
			begin
				match optarg with
				| Some "b" -> p.sc_mode <- W_bool;
				| Some "t" -> p.sc_mode <- W_tri;
				| Some "q" -> p.sc_mode <- W_quad;
				| Some s -> p.sc_mode <- W_num; p.sc_max <- safe_atoi s arg;
				| None -> p.sc_mode <- W_num;
			end;
		| "C", None -> p.sc_mode <- W_none;

		| "-min", None -> p.mincons <- true;
		| "-max", None -> p.maxcons <- true;

		| "z", None -> p.mcw_val <- 0;
		| "Z", None -> p.mcw_val <- 1;

		| "-w0", _ ->
			begin
				match optarg with
				| None -> p.mcw_mode <- MCW_num;
				| Some "b" -> p.mcw_mode <- MCW_bool;
				| Some "c" -> p.mcw_mode <- MCW_const;
				| _ -> erro arg;
			end;

		| "-real", None -> p.base_ty <- TY_real;

		| "Sp", None -> p.sp_mode <- W_none;

		| "n", _ ->
			begin
				match optarg with
				| Some s -> params.max_narrowing <- safe_atoi s arg;
				| None -> params.max_narrowing <- 7;
			end;
		| "-N", None -> params.max_narrowing <- 0;
		| "-l", _ ->
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
		| "-smt", _ ->
			begin
				let cmd =
					match optarg with
					| None -> i := !i + 1; argv.(!i)
					| Some s -> s
				in
				match Str.split (Str.regexp "[ \t]+") cmd with
				| tool::options -> p.smt_tool <- (tool,options);
				| _ -> err "Please specify a valid SMT solver!";
			end;
		| "-z3", None -> p.smt_tool <- z3cmd;
		| "-cvc4", None -> p.smt_tool <- cvc4cmd; p.reset_mode <- RESET_reboot;
		| "-dup", None -> default := false; params.mode <- MODE_dup;
		| "-relative-test", None -> params.mode <- MODE_relative_test;
		| "t", mode ->
			default := false;
			begin
				match mode with
				| Some "id" -> params.mode <- MODE_id;
				| Some "ho" -> params.mode <- MODE_higher_xml;
				| Some str -> err ("Unknown transformation mode: " ^ str ^ "!");
				| _ -> params.mode <- MODE_through;
			end
		| _ -> erro arg;
	end else begin
		match arg with
		| "UNCURRY" ->
			default := false;
			if p.dp then err "UNCURRY after EDG is not yet supported!";
			params.uncurry <- true;
		| "EDG" ->
			default := false;
			params.mode <- MODE_dp;
			if p.dp then err "'EDG' cannot be applied twice!";
			apply_edg ();
		| "LOOP" ->
			default := false;
			if not p.dp then err "LOOP cannot be applied before EDG!";
			params.max_loop <- 3;
		| "WPO" ->
			default := false;
			apply_wpo ();
		| "LPO" ->
			default := false;
			apply_lpo ();
		| "MPO" ->
			default := false;
			register_order
			{
				order_default with
				ext_lex = false;
				ext_mset = true;
				max_mode = MAX_all;
				sp_mode = W_none;
				status_mode = S_total;
			};
		| "RPO" ->
			default := false;
			register_order
			{
				order_default with
				ext_lex = true;
				ext_mset = true;
				max_mode = MAX_all;
				sp_mode = W_none;
				status_mode = S_total;
			};
		| "KBO" ->
			default := false;
			register_order
			{
				order_default with
				ext_lex = true;
				w_mode = W_num;
				mcw_val = 1;
				adm = true;
				status_mode = S_total;
			};
		| "POLO" ->
			default := false;
			apply_polo ();
		| _ ->
			if params.file <> "" then err ("too many input file: " ^ arg ^ "!");
			params.file <- arg;
	end;
	i := !i + 1;
done;
if !default then begin
	(* the default strategy *)
	params.mode <- MODE_dp;
	apply_polo ();
	!pp.sc_mode <- W_bool;
	params.uncurry <- true;
	apply_edg ();
	apply_polo ();
	apply_polo ();
	!pp.max_mode <- MAX_all;
	!pp.refer_w <- true;
	apply_lpo ();
	apply_polo ();
	!pp.max_mode <- MAX_dup;
	!pp.refer_w <- true;
	!pp.w_neg <- true;
	apply_wpo ();
	!pp.status_mode <- S_partial;
	!pp.max_mode <- MAX_dup;
	apply_polo ();
	!pp.w_dim <- 2;
(*	!pp.use_scope <- false;
	!pp.use_scope_ratio <- 0;
*)	params.max_loop <- 3;
end

type comment_type =
| CMT_error
| CMT_frame
| CMT_proof
| CMT_debug

let guard test os =
	if test then
		fun proc -> proc os
	else
		fun _ -> ()
let warning = guard params.warning stderr
let comment = guard params.comment stderr
let problem = guard params.problem stderr
let cpf = guard params.cpf stdout
let proof = guard params.proof stderr
let debug = guard params.debug stderr
let debug2 = guard params.debug2 stderr
