(* Contains AST that parser will target. It is the extracted AST. *)

(* Nat is a unary inductive and rgn/id/lab alias nat in our Coq development. 
 * Thanks to ninja extraction, we can target nat to int and the aliases to 
 * strings. *)
type nat = int
type rgn = string
type id = string
type lab = string

type cond =
| Cond_eq
| Cond_ne
| Cond_ugt
| Cond_uge
| Cond_ult
| Cond_ule
| Cond_sgt
| Cond_sge
| Cond_slt
| Cond_sle

type fcond =
| Fcond_false
| Fcond_oeq
| Fcond_ogt
| Fcond_oge
| Fcond_olt
| Fcond_ole
| Fcond_one
| Fcond_ord
| Fcond_ueq
| Fcond_ugt
| Fcond_uge
| Fcond_ult
| Fcond_ule
| Fcond_une
| Fcond_uno
| Fcond_true

type binop =
| Binop_add
| Binop_sub
| Binop_mul
| Binop_udiv
| Binop_sdiv
| Binop_urem
| Binop_srem
| Binop_shl
| Binop_lshr
| Binop_ashr
| Binop_and
| Binop_or
| Binop_xor

type fbinop =
| Fbinop_add
| Fbinop_sub
| Fbinop_mul
| Fbinop_div
| Fbinop_rem

type iconv =
| Iconv_trunc
| Iconv_zext
| Iconv_sext
| Iconv_fptoui
| Iconv_fptosi

type fconv =
| Fconv_fptrunc
| Fconv_fpext
| Fconv_uitofp
| Fconv_sitofp

type typ =
| Typ_float
| Typ_double
| Typ_int of nat
| Typ_ptr of typ * rgn
| Typ_name of id * rgn list
| Typ_fun of rgn list * typ list * typ option
| Typ_array of typ * int
| Typ_ptrU of int * rgn

type ftyp =
| Ftyp_float
| Ftyp_double
| Ftyp_int of nat
| Ftyp_ptr of typ * rgn
| Ftyp_fun of rgn list * typ list * typ option
| Ftyp_ptrU of int * rgn

type ftyps = ftyp list

type const =
| Const_null
| Const_nullU
| Const_float of float (* used to be binary64 *)
| Const_double of float
| Const_int of nat * int (* used to be Word.int *)
| Const_fun of lab
| Const_undef of ftyps
| Const_baddr of lab * lab

type operand =
| Op_reg of id
| Op_const of const

type insn =
| Insn_binop of id * binop * operand * operand
| Insn_fbinop of id * fbinop * operand * operand
| Insn_icmp of id * cond * operand * operand
| Insn_fcmp of id * fcond * operand * operand
| Insn_select of id * typ * operand * typ * operand * typ * operand
| Insn_load of id * typ * operand
| Insn_store of typ * operand * typ * operand
| Insn_poolcheck of id * rgn * typ * operand
| Insn_free of typ * operand
| Insn_gep of id * typ * operand * typ * operand
| Insn_gep1 of id * typ * operand * operand
| Insn_extractvalue of id * typ * operand * typ * const
| Insn_insertvalue of id * typ * operand * typ * operand * const
| Insn_iconv of id * iconv * typ * operand * typ
| Insn_fconv of id * fconv * typ * operand * typ
| Insn_bitcast of id * typ * operand * typ
| Insn_ptrtoint of id * typ * operand * typ
| Insn_inttoptr of id * typ * operand * typ
| Insn_gepU of id * typ * operand * operand
| Insn_poolcheckU of id * rgn * int * operand
| Insn_exit

type unsafe_opcode =
| Opcode_unknown of string

type insn_nd =
| Insn_call of id option * typ option * operand * rgn list * operand list
   * lab
| Insn_malloc of id * typ option * rgn * operand * lab
| Insn_unsafe_call of (id * typ) option * unsafe_opcode * operand list * lab

type terminator =
| Insn_return of typ * operand
| Insn_return_void
| Insn_br_uncond of lab
| Insn_br of operand * lab * lab
(* used to be ((typ, const) prod, lab) prod list *)
| Insn_switch of typ * operand * lab * ((typ * const) * lab) list
| Insn_indirect_br of typ * operand * lab list
| Insn_unreachable

type insn_nd_term =
| Insn_nd of insn_nd
| Insn_term of terminator

type phinode =
(* used to be (operand, lab) prod list *)
| Insn_phi of id * typ * (operand * lab) list

type phiblock = phinode list

type block = { b_lab : lab; b_phis : phiblock; b_insns : insn list;
               b_nd_term : insn_nd_term }

type blocks = block list

(* used to be (rgn, typ) prod list *)
type function0 = { f_lab : lab; f_params : id list; f_sig : typ list;
                   f_body : blocks; f_ret : typ option;
                   f_prgn : (rgn * typ) list;
                   f_lrgn : (rgn * typ) list }

type functions = function0 list
