open BasicAst
open Byte
open Datatypes
open EAst
open EPrimitive
open Kernames
open List0
open MCString
open Specif
open Bytestring

(** val decompose_app_rec : term -> term list -> term * term list **)

let rec decompose_app_rec t0 l =
  match t0 with
  | Coq_tApp (f, a) -> decompose_app_rec f (a :: l)
  | _ -> (t0, l)

(** val decompose_app : term -> term * term list **)

let decompose_app f =
  decompose_app_rec f []

(** val isBox : term -> bool **)

let isBox = function
| Coq_tBox -> true
| _ -> false

(** val string_of_def : ('a1 -> String.t) -> 'a1 def -> String.t **)

let string_of_def f def0 =
  String.append (String.String (Coq_x28, String.EmptyString))
    (String.append (string_of_name def0.dname)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (f def0.dbody)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_nat def0.rarg) (String.String (Coq_x29,
              String.EmptyString)))))))

(** val maybe_string_of_list : ('a1 -> String.t) -> 'a1 list -> String.t **)

let maybe_string_of_list f l = match l with
| [] -> String.EmptyString
| _ :: _ -> string_of_list f l

(** val string_of_term : term -> String.t **)

let rec string_of_term = function
| Coq_tBox ->
  String.String (Coq_xe2, (String.String (Coq_x88, (String.String (Coq_x8e,
    String.EmptyString)))))
| Coq_tRel n ->
  String.append (String.String (Coq_x52, (String.String (Coq_x65,
    (String.String (Coq_x6c, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_nat n) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tVar n ->
  String.append (String.String (Coq_x56, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append n (String.String (Coq_x29, String.EmptyString)))
| Coq_tEvar (ev, _) ->
  String.append (String.String (Coq_x45, (String.String (Coq_x76,
    (String.String (Coq_x61, (String.String (Coq_x72, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_nat ev)
      (String.append (String.String (Coq_x5b, (String.String (Coq_x5d,
        String.EmptyString)))) (String.String (Coq_x29, String.EmptyString))))
| Coq_tLambda (na, t1) ->
  String.append (String.String (Coq_x4c, (String.String (Coq_x61,
    (String.String (Coq_x6d, (String.String (Coq_x62, (String.String
    (Coq_x64, (String.String (Coq_x61, (String.String (Coq_x28,
    String.EmptyString))))))))))))))
    (String.append (string_of_name na)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term t1) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tLetIn (na, b, t1) ->
  String.append (String.String (Coq_x4c, (String.String (Coq_x65,
    (String.String (Coq_x74, (String.String (Coq_x49, (String.String
    (Coq_x6e, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_name na)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term b)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_term t1) (String.String (Coq_x29,
              String.EmptyString)))))))
| Coq_tApp (f, l) ->
  String.append (String.String (Coq_x41, (String.String (Coq_x70,
    (String.String (Coq_x70, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_term f)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term l) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tConst c ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_kername c) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tConstruct (i, n, args) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
    (String.String (Coq_x63, (String.String (Coq_x74, (String.String
    (Coq_x28, String.EmptyString))))))))))))))))))))
    (String.append (string_of_inductive i)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n)
          (String.append (maybe_string_of_list string_of_term args)
            (String.String (Coq_x29, String.EmptyString))))))
| Coq_tCase (indn, t1, brs) ->
  let (ind, i) = indn in
  String.append (String.String (Coq_x43, (String.String (Coq_x61,
    (String.String (Coq_x73, (String.String (Coq_x65, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_inductive ind)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat i)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_term t1)
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append
                  (string_of_list (fun b -> string_of_term (snd b)) brs)
                  (String.String (Coq_x29, String.EmptyString)))))))))
| Coq_tProj (p, c) ->
  String.append (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x6a, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_inductive p.proj_ind)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat p.proj_npars)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_nat p.proj_arg)
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append (string_of_term c) (String.String (Coq_x29,
                  String.EmptyString)))))))))
| Coq_tFix (l, n) ->
  String.append (String.String (Coq_x46, (String.String (Coq_x69,
    (String.String (Coq_x78, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_list (string_of_def string_of_term) l)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tCoFix (l, n) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x46, (String.String (Coq_x69, (String.String
    (Coq_x78, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_list (string_of_def string_of_term) l)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tPrim p ->
  String.append (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x69, (String.String (Coq_x6d, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_prim string_of_term p) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tLazy t1 ->
  String.append (String.String (Coq_x4c, (String.String (Coq_x61,
    (String.String (Coq_x7a, (String.String (Coq_x79, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_term t1) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tForce t1 ->
  String.append (String.String (Coq_x46, (String.String (Coq_x6f,
    (String.String (Coq_x72, (String.String (Coq_x63, (String.String
    (Coq_x65, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_term t1) (String.String (Coq_x29,
      String.EmptyString)))

(** val prim_global_deps :
    (term -> KernameSet.t) -> term prim_val -> KernameSet.t **)

let prim_global_deps deps = function
| Coq_existT (_, p0) ->
  (match p0 with
   | Coq_primArrayModel a ->
     fold_left (fun acc x -> KernameSet.union (deps x) acc) a.array_value
       (deps a.array_default)
   | _ -> KernameSet.empty)

(** val term_global_deps : term -> KernameSet.t **)

let rec term_global_deps = function
| Coq_tLambda (_, x) -> term_global_deps x
| Coq_tLetIn (_, x, y) ->
  KernameSet.union (term_global_deps x) (term_global_deps y)
| Coq_tApp (x, y) ->
  KernameSet.union (term_global_deps x) (term_global_deps y)
| Coq_tConst kn -> KernameSet.singleton kn
| Coq_tConstruct (ind, _, args) ->
  let { inductive_mind = kn; inductive_ind = _ } = ind in
  fold_left (fun acc x -> KernameSet.union (term_global_deps x) acc) args
    (KernameSet.singleton kn)
| Coq_tCase (indn, x, brs) ->
  let (ind, _) = indn in
  KernameSet.union (KernameSet.singleton ind.inductive_mind)
    (fold_left (fun acc x0 ->
      KernameSet.union (term_global_deps (snd x0)) acc) brs
      (term_global_deps x))
| Coq_tProj (p, c) ->
  KernameSet.union (KernameSet.singleton p.proj_ind.inductive_mind)
    (term_global_deps c)
| Coq_tFix (mfix, _) ->
  fold_left (fun acc x -> KernameSet.union (term_global_deps x.dbody) acc)
    mfix KernameSet.empty
| Coq_tCoFix (mfix, _) ->
  fold_left (fun acc x -> KernameSet.union (term_global_deps x.dbody) acc)
    mfix KernameSet.empty
| Coq_tPrim p -> prim_global_deps term_global_deps p
| Coq_tLazy t1 -> term_global_deps t1
| Coq_tForce t1 -> term_global_deps t1
| _ -> KernameSet.empty
