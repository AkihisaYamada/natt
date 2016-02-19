open Util
open Term
open Trs
open Dp
open Params

let is_fun (Node(fty,_,_)) = fty = Fun

let uncurry aname nargs (trs:trs) (dg:dg) =
	let aarity_tbl = Hashtbl.create 64 in
	let aarity fname =
		try Hashtbl.find aarity_tbl fname
		with Not_found -> 0
	in
	let set_aarity ord fname d =
		try let aa = Hashtbl.find aarity_tbl fname in
			if ord aa d then Hashtbl.replace aarity_tbl fname d;
		with Not_found ->
			Hashtbl.add aarity_tbl fname d;
	in
	let rec dig d (Node(fty,fname,ss)) =
		if fname = aname then begin
			dig (d + 1) (hd ss);
			List.iter (dig 0) (tl ss);
		end else begin
			if fty = Fun then set_aarity (<) fname d;
			List.iter (dig 0) ss;
		end
	in
	let iterer _ rule = dig 0 rule#l; dig 0 rule#r; in
	trs#iter_rules iterer;
	dg#iter_dps iterer;

	let rec dig_hd d (Node(fty,fname,ss)) =
		if fname = aname then begin
			dig_hd (d + 1) (hd ss);
		end else begin
			if fty = Fun then set_aarity (>) fname d;
		end
	in
	let iterer _ rule = dig_hd 0 rule#l; in
	trs#iter_rules iterer;
	dg#iter_dps iterer;

	let uncurry_name fname i =
		aname ^ "^" ^ string_of_int i ^ "_" ^ fname
	in

	let uncurry_top (fty,fname,ss,d,aa) =
		Node(fty, (if d > 0 then uncurry_name fname d else fname), ss)
	in
	let rec uncurry_term s = uncurry_top (uncurry_sub s)
	and uncurry_sub (Node(fty,fname,ss)) =
		if fname = aname then
			match ss with
			| [] -> raise (Internal "uncurry")
			| t::ss ->
				let (gty, gname, ts, d, aa) as t' = uncurry_sub t in
				let ss = List.map uncurry_term ss in
				if d < aa then
					(gty, gname, ts @ ss, d + 1, aa)
				else
					(fty, fname, uncurry_top t'::ss, 0, 0)
		else
			(fty, fname, List.map uncurry_term ss, 0, aarity fname)
	in
	trs#iter_rules (fun i rule -> trs#modify_rule i (uncurry_term rule#l) (uncurry_term rule#r););
	dg#iter_dps (fun i dp -> dg#modify_dp i (uncurry_term dp#l) (uncurry_term dp#r););

	let varlist name start count =
		let last = start + count - 1 in
		let rec sub i =
			if i > last then []
			else Node(Var, name ^ string_of_int i, [])::sub (i+1)
		in
		sub start
	in
	let iterer fname aa =
		if aa > 0 then begin
			match (trs#find_sym fname).arity with
			| Arity n ->
				let args = ref (varlist "_" 1 n) in
				let r = ref (Node(Fun, fname, !args)) in
				for i = 1 to aa do
					(trs#get_sym (uncurry_name fname i)).arity <- Arity (n + i * nargs);
					let new_args = varlist "_" (n + i * nargs) nargs in
					let l = Node(Fun, aname, !r :: new_args) in
					args := !args @ new_args;
					r := Node(Fun, uncurry_name fname i, !args);
					trs#add_rule (weak_rule l !r);
				done;
			| _ -> raise (Internal "app")
		end;
	in
	Hashtbl.iter iterer aarity_tbl;;

exception Next

let auto_uncurry (trs:trs) (dg:dg) =
	let folder aname ainfo anames =
		try
			if ainfo.symtype <> Fun then raise Next;
			if Rules.is_empty ainfo.defined_by then raise Next;
			let nargs =
				match ainfo.arity with
				| Arity n -> if n > 0 then n - 1 else raise Next
				| _ -> raise Next
			in
			let sub good bad =
				let rec sub2 d (Node(fty,fname,ss)) =
					if fname = aname then begin
						sub2 (d+1) (hd ss);
						List.iter (sub2 0) (tl ss);
					end else begin
						if d > 0 then
							if fty <> Fun || trs#defines fname then bad d else good d;
						List.iter (sub2 0) ss;
					end
				in
				sub2 0
			in
			let iterer_l _ lr = sub (fun _ -> ()) (fun _ -> raise Next) lr#l in
			trs#iter_rules iterer_l;
			dg#iter_dps iterer_l;

			let ngoods = ref 0 in
			let nbads = ref 0 in
			let add r n = r := !r + n in
			let iterer_r _ lr = sub (add ngoods) (add nbads) lr#r in
			trs#iter_rules iterer_r;
			dg#iter_dps iterer_r;

			debug (fun _ ->
				prerr_string ("  Uncurrying evaluation for " ^ aname ^ ": " ^
				string_of_int !ngoods ^ " vs. " ^
				string_of_int !nbads ^ "");
			);

			if !ngoods = 0 (*|| !ngoods < !nbads*) then begin
				raise Next;
			end;
			uncurry aname nargs trs dg;
			aname::anames
		with Next -> anames
	in
(*
	let compare_occurrence fname gname =
		(trs#find_sym gname).occurence - (trs#find_sym fname).occurence
	in
	let app_candidates = List.sort compare_occurrence trs#get_defsyms in
*)
	trs#fold_syms folder []
