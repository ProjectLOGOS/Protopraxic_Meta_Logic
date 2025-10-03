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

(** val string_of_name : name -> String.t **)

let string_of_name = function
| Coq_nAnon -> String.String (Coq_x5f, String.EmptyString)
| Coq_nNamed n -> n

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

(** val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def **)

let map_def tyf bodyf d =
  { dname = d.dname; dtype = (tyf d.dtype); dbody = (bodyf d.dbody); rarg =
    d.rarg }

type 'term mfixpoint = 'term def list

(** val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool **)

let test_def tyf bodyf d =
  (&&) (tyf d.dtype) (bodyf d.dbody)

type ('universe, 'term) judgment_ = { j_term : 'term option; j_typ : 
                                      'term; j_univ : 'universe option }

type 'term context_decl = { decl_name : aname; decl_body : 'term option;
                            decl_type : 'term }

(** val map_decl : ('a1 -> 'a2) -> 'a1 context_decl -> 'a2 context_decl **)

let map_decl f d =
  { decl_name = d.decl_name; decl_body = (option_map f d.decl_body);
    decl_type = (f d.decl_type) }

(** val map_context :
    ('a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list **)

let map_context f c =
  map (map_decl f) c

(** val test_decl : ('a1 -> bool) -> 'a1 context_decl -> bool **)

let test_decl f d =
  (&&) (option_default f d.decl_body true) (f d.decl_type)

(** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

let snoc _UU0393_ d =
  d :: _UU0393_

(** val app_context : 'a1 list -> 'a1 list -> 'a1 list **)

let app_context _UU0393_ _UU0393_' =
  app _UU0393_' _UU0393_

type ('a, 'p) ondecl = __ * 'p

(** val test_context : ('a1 -> bool) -> 'a1 context_decl list -> bool **)

let rec test_context f = function
| [] -> true
| d :: _UU0393_ -> (&&) (test_context f _UU0393_) (test_decl f d)

(** val test_context_k :
    (nat -> 'a1 -> bool) -> nat -> 'a1 context_decl list -> bool **)

let rec test_context_k f k = function
| [] -> true
| d :: _UU0393_ ->
  (&&) (test_context_k f k _UU0393_)
    (test_decl (f (add (length _UU0393_) k)) d)

type ('term, 'p) onctx_k = ('term context_decl, ('term, 'p) ondecl) coq_Alli

(** val ondeclP :
    ('a1 -> bool) -> 'a1 context_decl -> ('a1 -> 'a2 reflectT) -> ('a1, 'a2)
    ondecl reflectT **)

let ondeclP p d hr =
  let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } = d in
  let r = hr decl_type0 in
  (match r with
   | ReflectT p0 ->
     let r0 = reflect_option_default p hr decl_body0 in
     (match r0 with
      | ReflectT o -> ReflectT (o, p0)
      | ReflectF -> ReflectF)
   | ReflectF -> ReflectF)

(** val fold_context_k :
    (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list **)

let fold_context_k f _UU0393_ =
  List0.rev (mapi (fun k' decl -> map_decl (f k') decl) (List0.rev _UU0393_))
