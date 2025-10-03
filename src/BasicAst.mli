open All_Forall
open Byte
open Datatypes
open Kernames
open List0
open MCList
open MCOption
open MCReflect
open Nat0
open Bytestring

type __ = Obj.t

type name =
| Coq_nAnon
| Coq_nNamed of ident

type relevance =
| Relevant
| Irrelevant

type 'a binder_annot = { binder_name : 'a; binder_relevance : relevance }

type aname = name binder_annot

val string_of_name : name -> String.t

type cast_kind =
| VmCast
| NativeCast
| Cast

type case_info = { ci_ind : inductive; ci_npar : nat; ci_relevance : relevance }

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

type conv_pb =
| Conv
| Cumul

type 'term def = { dname : aname; dtype : 'term; dbody : 'term; rarg : nat }

val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def

type 'term mfixpoint = 'term def list

val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool

type ('universe, 'term) judgment_ = { j_term : 'term option; j_typ : 
                                      'term; j_univ : 'universe option }

type 'term context_decl = { decl_name : aname; decl_body : 'term option;
                            decl_type : 'term }

val map_decl : ('a1 -> 'a2) -> 'a1 context_decl -> 'a2 context_decl

val map_context :
  ('a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list

val test_decl : ('a1 -> bool) -> 'a1 context_decl -> bool

val snoc : 'a1 list -> 'a1 -> 'a1 list

val app_context : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) ondecl = __ * 'p

val test_context : ('a1 -> bool) -> 'a1 context_decl list -> bool

val test_context_k :
  (nat -> 'a1 -> bool) -> nat -> 'a1 context_decl list -> bool

type ('term, 'p) onctx_k = ('term context_decl, ('term, 'p) ondecl) coq_Alli

val ondeclP :
  ('a1 -> bool) -> 'a1 context_decl -> ('a1 -> 'a2 reflectT) -> ('a1, 'a2)
  ondecl reflectT

val fold_context_k :
  (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list
