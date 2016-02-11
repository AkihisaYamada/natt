open Params
open Term
open Trs
open Util

type result =
| YES
| MAYBE
| NO

(* static usable rules *)
let static_usable_rules (trs:Trs.t) dg used_dpset =
	if dg#minimal then (
		let used = Hashtbl.create 128 in
		let rec sub (Node(_,_,ts) as t) =
			let iterer i =
				if not (Hashtbl.mem used i) then begin
					let (_,r) = trs#find_rule i in
					Hashtbl.add used i ();
					sub r;
				end;
			in
			List.iter iterer (trs#find_matchable t);
			List.iter sub ts;
		in
		IntSet.iter (fun i -> let (_,Node(_,_,ts)) = dg#find_dp i in List.iter sub ts) used_dpset;
	
		trs#fold_rules
		(fun i _ (usables,unusables) ->
			if Hashtbl.mem used i then (i::usables,unusables) else (usables,i::unusables)
		) ([],[])
	) else (
		trs#fold_rules (fun i _ is -> i::is) [], []
	)

let uncurry =
	if params.uncurry then
		fun trs dg ->
			comment (fun _ -> prerr_string "Uncurrying");
			let appsyms = App.auto_uncurry trs dg in
			if StrSet.is_empty appsyms then
				(comment (fun _ -> prerr_endline " ... failed."); false)
			else
			(	comment
				(fun _ ->
					StrSet.iter (fun aname -> prerr_string " "; prerr_string aname) appsyms;
					prerr_newline ();
				);
				problem trs#output;
				true
			)
	else
		fun _ _ -> false


let relative_test (trs:Trs.t) =
	trs#exists_eq (fun i (l,r) ->
		if duplicating l r then (
			comment (fun os ->
				output_string os "Weak rule e";
				output_string os (string_of_int i);
				output_string os " is duplicating\n";
				flush os;
			);
			true
		) else if not(trs#const_term r) then (
			comment (fun os ->
				output_string os "Weak rule e";
				output_string os (string_of_int i);
				output_string os " calls a strict rule\n";
				flush os;
			);
			true
		) else false
	);;

let theory_test trs =
	let ths = trs#get_ths in
	if StrSet.is_empty ths then false
	else
		let ths = StrSet.remove "C" ths in
		let ths = StrSet.remove "AC" ths in
		if StrSet.is_empty ths then true
		else (
			warning (fun _ -> prerr_endline ("Unacceptable theories: " ^ StrSet.fold (^) ths ""));
			raise Unknown
		)

(* extra variable test *)
let extra_test trs =
	let iterer i (l,r) =
		let lvars = varlist l in
		let rvars = varlist r in
		if List.exists (fun rvar -> not (List.mem rvar lvars)) rvars then
		begin
			proof
			(fun _ ->
				prerr_string "Extra variable in rule ";
				prerr_int i;
				prerr_endline ".";
			);
			raise Nonterm;
		end;
	in
	trs#iter_rules iterer;;

(* remove trivial relative rules *)
let clean_eqs trs =
	let iterer i (l,r) =
		if l = r then begin
			proof (fun _ ->
				prerr_string "Removing trivial relative rule e";
				prerr_int i;
				prerr_endline ".";
			);
			trs#remove_eq i;
		end;
	in
	trs#iter_eqs iterer;;


(* rule removal processor *)
let dummy_dg = new Dp.dg (new Trs.t)

let rule_remove trs =
	if Array.length params.orders_removal > 0 then begin
		let proc_list =
			let folder p procs =
				new Wpo.processor p trs dummy_dg :: procs
			in
			Array.fold_right folder params.orders_removal []
		in
		let remove_strict rules =
			List.exists (fun proc -> proc#direct rules) proc_list
		in
		let rec loop () =
			let rules = trs#fold_rules (fun i _ is -> i::is) [] in
			comment (fun _ ->
				prerr_string "Number of Rules: ";
				prerr_int trs#get_size;
				prerr_newline ();
			);
			if trs#get_size = 0 then raise Success
			else if remove_strict rules then begin
				loop ();
			end else begin
				comment (fun _ -> prerr_endline " failed.");
			end;
		in
		loop ();
	end;;

(* reduction pair processor *)
let dp_remove trs dg =
	let sccs = ref dg#get_sccs in
	let remove_unusable () =
		let init = ref true in
		let used_dpset = List.fold_left IntSet.union IntSet.empty !sccs in
		let curr_len = IntSet.cardinal used_dpset in
		if !init || curr_len < dg#get_size then
		begin
			log (fun _ -> prerr_string "Removing unrelated DPs: {");
			init := false;
			let dp_remover i _ =
				if not (IntSet.mem i used_dpset) then
				begin
					log (fun _ -> prerr_string " #"; prerr_int i;);
					dg#remove_dp i;
				end;
			in
			dg#iter_dps dp_remover;
			log (fun _ -> prerr_endline " }");
(*
			log (fun _ -> prerr_string "Removing unusable rules: {");
			let (_,unusables) = static_usable_rules trs dg used_dpset in
			let rule_remover i =
				log (fun _ -> prerr_string " "; prerr_int i;);
				trs#remove_rule i;
			in
			List.iter rule_remover unusables;
			log (fun _ -> prerr_endline " }");
*)
		end;
	in
	let scc_sorter =
		let scc_size scc =
			IntSet.fold (fun i r -> dg#get_dp_size i + r) scc 0
		in
		match params.sort_scc with
		| SORT_asc ->
			List.sort (fun scc1 scc2 -> compare (scc_size scc1) (scc_size scc2))
		| SORT_desc ->
			List.sort (fun scc1 scc2 -> compare (scc_size scc1) (scc_size scc2))
		| SORT_none ->
			fun sccs -> sccs
	in
	sccs := scc_sorter !sccs;
	let given_up = ref false in
	let proc_list =
		Array.fold_right
		(fun p procs ->
			p.usable <- p.usable && dg#minimal;
			new Wpo.processor p trs dg :: procs
		)
		params.orders_dp []
	in
	let remove_strict sccref =
		let (usables,_) = static_usable_rules trs dg !sccref in
		List.exists (fun proc -> proc#reduce dg usables sccref) proc_list
	in
	let rec loop () =
		comment (fun _ ->
			prerr_string "Number of SCCs: ";
			prerr_int (List.length !sccs);
			prerr_newline (););
		remove_unusable ();
		match !sccs with
		| [] ->
			cpf (fun os -> output_string os "</proof>";);
			if !given_up then raise Unknown else raise Success
		| scc::rest ->
			problem
			(fun _ ->
				let folder i abbr = abbr#add i in
				prerr_string "  SCC {";
				(IntSet.fold folder scc (new Abbrev.for_int stderr " #"))#close;
				prerr_string " }\n    ";
			);
			if IntSet.for_all dg#is_weak scc then begin
				comment (fun _ -> prerr_endline "only weak rules.");
				sccs := rest;
				loop ();
			end else begin
				let sccref = ref scc in
				if remove_strict sccref then begin
					sccs := scc_sorter (dg#get_subsccs !sccref) @ rest;
					debug dg#output;
					loop ();
				end else begin
					comment
					(fun _ ->
						prerr_endline "failed.";
					);
					Nonterm.find_loop params.max_loop trs dg scc;
				end
			end
	in
	loop ();;


let prove_termination (trs:Trs.t) =
	problem (fun os ->
		output_string os "Input TRS:\n";
		trs#output os;
	);
	cpf (fun os ->
		output_string os "<input>\n <trsInput>\n";
		trs#output_xml os;
		output_string os 
" </trsInput>
</input>
<cpfVersion>2.2</cpfVersion>
<proof>
 <trsTerminationProof>
"
	);

	let ret = try

		let theoried = theory_test trs in

		extra_test trs;

		clean_eqs trs;

		rule_remove trs;

		if uncurry trs dummy_dg then rule_remove trs;

		if params.mode = MODE_order then raise Unknown;
		if params.rdp_mode = RDP_naive && relative_test trs then raise Unknown;

		if theoried && params.acdp_mode = ACDP_new then begin
			try let dg = new Dp.dg trs in
				dg#init;
				problem (fun _ ->
					prerr_endline "Dependency Pairs:";
					dg#output_dps stderr;
				);
				debug dg#output;
				dp_remove trs dg;
			with
			| Success ->
				let dg = new Dp.dg trs in
				dg#init_ac_ext;
				problem (fun _ ->
					prerr_endline "AC Extensions:";
					dg#output_dps stderr;
				);
				dp_remove trs dg;
		end else begin
			let dg = new Dp.dg trs in
			dg#init;
			problem (fun _ ->
				prerr_endline "Dependency Pairs:";
				dg#output_dps stderr;
			);
			dp_remove trs dg;
		end;
		raise Unknown;
	with
	| Success -> YES
	| Unknown -> MAYBE
	| Nonterm -> NO
in
	cpf (fun os -> output_string os
" </trsTerminationProof>
</proof>
<origin>
 <proofOrigin>
  <tool>
   <name>NaTT</name>
   <version>";
   output_string os version;
   output_string os
"</version>
  </tool>
 </proofOrigin>
</origin>
"
	);
	ret
;;

class main =
	let err msg = prerr_endline ("Error: " ^ msg ^ "!"); exit 1 in
	let warn msg = warning(fun _ -> prerr_endline ("Warning: " ^ msg ^ ".")) in
	object (x)
		val trs = new Trs.t

		method no_ac = not(StrSet.mem "AC" trs#get_ths)

		method duplicating =
			trs#exists_rule (fun _ (l,r) -> dupvarlist l r <> [])

		method run =
			if params.file = "" then
				trs#read_stdin
			else
				trs#read params.file;

			cpf (fun os ->
				output_string os
"<?xml version=\"1.0\"?>
<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>
<certificationProblem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"cpf.xsd\">
";
			);

			begin match params.mode with
			| MODE_higher_xml ->
				trs#output_xml_ho stdout;
			| MODE_through ->
				trs#output stdout;
			| MODE_flat ->
				trs#iter_rules (fun i (l,r) -> trs#replace_rule i (flat l) (flat r));
				trs#output stdout;
			| MODE_uncurry ->
				ignore (App.auto_uncurry trs (new Dp.dg trs));
				trs#output stdout;
			| MODE_simple ->
				if trs#exists_rule (fun _ (l,r) -> emb_le l r) then
					err "Not simple";
			| MODE_dup	->
				if x#duplicating then err "Duplicating TRS";
				warn "Non-duplicating TRS";
				exit 0;
			| MODE_id	->
				trs#iter_rules (fun i (l,r) -> if term_eq l r then trs#remove_rule i);
				trs#output_wst stdout;
			| MODE_dist	->
				let sub _ (l,r) =
					match r with
					| Node(Th "AC",_,
						[Node(Th "AC",_,[Node(Var,_,_); Node(Var,_,_)]);
						 Node(Th "AC",_,[Node(Var,_,_); Node(Var,_,_)]);
						]) ->
						(match l with
						 | Node(Th "AC",_,
						 	[Node(Var,_,_);
							 Node(Th "AC",_,[Node(Var,_,_);Node(Var,_,_)]);
							]) -> true
						 | Node(Th "AC",_,
							[Node(Th "AC",_,[Node(Var,_,_);Node(Var,_,_)]);
							 Node(Var,_,_);
							]) -> true
						 | _ -> false
						)
					| _ -> false
				in
				if trs#exists_rule sub then
					print_endline "Distribution like rule"
				else if x#duplicating then
					print_endline "Duplicating TRS"
				else
					print_endline "";
			| MODE_relative_test ->
				if relative_test trs then exit 1;
			| _ ->
				Array.iter
					(fun p ->
						if not p.remove_all && nonmonotone p then
							err "Rule removal processor must be monotone";
					) params.orders_removal;
				let ans = prove_termination trs in
(*				cpf (fun os ->
					output_string os
					(	match ans with
						| YES	-> "<yes>"
						| NO	-> "<no>"
						| MAYBE	-> "<maybe>"
					);
					output_char os '\n';
				);
*)				cpf (fun os -> output_string os "</certificationProblem>\n");
				if not params.cpf then
					print_endline
					(	match ans with
						| YES	-> "YES"
						| NO	-> "NO"
						| MAYBE	-> "MAYBE"
					);
			end;
	end;;

begin
	try
		(new main)#run;
		exit 0;
	with
	| Unsound s ->
		prerr_newline ();
		prerr_string "Unsound: ";
		prerr_endline s;
	| Proc.Dead cmd ->
		prerr_newline ();
		prerr_string "Proccess '";
		prerr_string cmd;
		prerr_endline "' is dead!";
	| Smt.Internal s ->
		prerr_newline ();
		prerr_string "SMT error: ";
		prerr_endline s;
	| Smt.Response(s,e) ->
		prerr_newline ();
		prerr_string "Unexpected SMT solver response to '";
		prerr_string s;
		prerr_endline "':";
		Smt.prerr_exp e;
		prerr_newline ();
	| No_support(s) ->
		prerr_newline ();
		prerr_string "Not supported: ";
		prerr_endline s;
end;
print_endline "ERR";
exit 1;

