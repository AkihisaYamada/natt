open Util
open Smt


class wpo_sym (sym:#Trs.sym_detailed) = object
  val base : Trs.sym_detailed = sym
  method base = base
  val mutable sum = false
  val mutable max = false
  val mutable maxpol = false
  val mutable status_mode = Params.S_none
  val mutable weight = LI 0
  val mutable subterm_coef : int -> exp = k_comb (LI 1)
  val mutable subterm_penalty : int -> exp = k_comb (LI 0)
  val mutable maxfilt : int -> exp = k_comb (LB false)
  val mutable argfilt : int -> exp = k_comb Nil
  val mutable argfilt_list = LB true
  val mutable is_const = LB(sym#arity = 0)
  val mutable is_quasi_const = LB(sym#arity = 0)
  val mutable perm : int -> int -> exp = k_comb (k_comb (LB false))
  val mutable permed : int -> exp = k_comb (LB false)
  val mutable mapped : int -> exp = k_comb (LB false)
  val mutable mset_status = LB false
  val mutable prec = LI 0
  method max = max
  method maxpol = maxpol
  method status_mode = status_mode
  method weight = weight
  method subterm_coef = subterm_coef
  method subterm_penalty = subterm_penalty
  method maxfilt = maxfilt
  method argfilt = argfilt
  method argfilt_list = argfilt_list
  method is_const = is_const
  method is_quasi_const = is_quasi_const
  method perm = perm
  method permed = permed
  method mapped = mapped
  method mset_status = mset_status
  method lex_status = smt_not mset_status
  method prec = prec
  method set_max x = max <- x
  method set_maxpol x = maxpol <- x
  method set_status_mode x = status_mode <- x
  method set_weight x = weight <- x
  method set_subterm_coef x = subterm_coef <- x
  method set_subterm_penalty x = subterm_penalty <- x
  method set_maxfilt x = maxfilt <- x
  method set_argfilt x = argfilt <- x
  method set_argfilt_list x = argfilt_list <- x
  method set_is_const x = is_const <- x
  method set_is_quasi_const x = is_quasi_const <- x
  method set_perm x = perm <- x
  method set_permed x = permed <- x
  method set_mapped x = mapped <- x
  method set_mset_status x = mset_status <- x
  method set_prec x = prec <- x
end
