open BasicAst
open Byte
open Datatypes
open EAst
open EAstUtils
open EGlobalEnv
open EPrimitive
open Kernames
open List0
open MCString
open Nat0
open Show
open Specif
open Universes0
open Bytestring

(** val lookup_ind_decl :
    global_declarations -> kername -> nat -> one_inductive_body option **)

let lookup_ind_decl _UU03a3_ ind i =
  match lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | ConstantDecl _ -> None
     | InductiveDecl m ->
       let { ind_finite = _; ind_npars = _; ind_bodies = l } = m in
       nth_error l i)
  | None -> None

(** val is_fresh : context -> ident -> bool **)

let is_fresh _UU0393_ id =
  forallb (fun decl ->
    match decl.decl_name with
    | Coq_nAnon -> true
    | Coq_nNamed id' -> negb (IdentOT.reflect_eq_string id id')) _UU0393_

(** val name_from_term : term -> String.t **)

let rec name_from_term = function
| Coq_tRel _ -> String.String (Coq_x48, String.EmptyString)
| Coq_tVar _ -> String.String (Coq_x48, String.EmptyString)
| Coq_tEvar (_, _) -> String.String (Coq_x48, String.EmptyString)
| Coq_tLambda (_, _) -> String.String (Coq_x66, String.EmptyString)
| Coq_tLetIn (_, _, t') -> name_from_term t'
| Coq_tApp (f, _) -> name_from_term f
| Coq_tConst _ -> String.String (Coq_x78, String.EmptyString)
| _ -> String.String (Coq_x55, String.EmptyString)

(** val fresh_id_from : context -> nat -> String.t -> String.t **)

let fresh_id_from _UU0393_ n id =
  let rec aux i = match i with
  | O -> id
  | S i' ->
    let id' = String.append id (string_of_nat (sub n i)) in
    if is_fresh _UU0393_ id' then id' else aux i'
  in aux n

(** val fresh_name : context -> name -> term -> name **)

let fresh_name _UU0393_ na t0 =
  let id = match na with
           | Coq_nAnon -> name_from_term t0
           | Coq_nNamed id -> id
  in
  if is_fresh _UU0393_ id
  then Coq_nNamed id
  else Coq_nNamed
         (fresh_id_from _UU0393_ (S (S (S (S (S (S (S (S (S (S O)))))))))) id)

module PrintTermTree =
 struct
  (** val print_def : ('a1 -> Tree.t) -> 'a1 def -> Tree.t **)

  let print_def f def0 =
    Tree.Coq_append ((Tree.Coq_string (string_of_name def0.dname)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
      (String.String (Coq_x7b, (String.String (Coq_x20, (String.String
      (Coq_x73, (String.String (Coq_x74, (String.String (Coq_x72,
      (String.String (Coq_x75, (String.String (Coq_x63, (String.String
      (Coq_x74, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_nat def0.rarg)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x7d,
      String.EmptyString))))), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x3a, (String.String
      (Coq_x3d, (String.String (Coq_x20, String.EmptyString))))))))),
      (Tree.Coq_append ((Tree.Coq_string nl), (f def0.dbody))))))))))))

  (** val print_defs :
      (context -> bool -> bool -> term -> Tree.t) -> context_decl list ->
      term mfixpoint -> Tree.t **)

  let print_defs print_term0 _UU0393_ defs =
    let ctx' = map (fun d -> { decl_name = d.dname; decl_body = None }) defs
    in
    Tree.print_list (print_def (print_term0 (app ctx' _UU0393_) true false))
      (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_string (String.String
      (Coq_x20, (String.String (Coq_x77, (String.String (Coq_x69,
      (String.String (Coq_x74, (String.String (Coq_x68, (String.String
      (Coq_x20, String.EmptyString))))))))))))))) defs

  (** val print_prim : (term -> Tree.t) -> term prim_val -> Tree.t **)

  let print_prim soft p =
    match projT2 p with
    | Coq_primIntModel f ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
        (Coq_x74, (String.String (Coq_x3a, (String.String (Coq_x20,
        String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
        (show show_uint f)), (Tree.Coq_string (String.String (Coq_x29,
        String.EmptyString))))))
    | Coq_primFloatModel f ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x66, (String.String (Coq_x6c, (String.String
        (Coq_x6f, (String.String (Coq_x61, (String.String (Coq_x74,
        (String.String (Coq_x3a, (String.String (Coq_x20,
        String.EmptyString))))))))))))))))), (Tree.Coq_append
        ((Tree.Coq_string (show show_float f)), (Tree.Coq_string
        (String.String (Coq_x29, String.EmptyString))))))
    | Coq_primStringModel f ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x73, (String.String (Coq_x74, (String.String
        (Coq_x72, (String.String (Coq_x69, (String.String (Coq_x6e,
        (String.String (Coq_x67, (String.String (Coq_x3a, (String.String
        (Coq_x20, String.EmptyString))))))))))))))))))), (Tree.Coq_append
        ((Tree.Coq_string (show show_pstring f)), (Tree.Coq_string
        (String.String (Coq_x29, String.EmptyString))))))
    | Coq_primArrayModel a ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x61, (String.String (Coq_x72, (String.String
        (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x79,
        (String.String (Coq_x3a, String.EmptyString))))))))))))))),
        (Tree.Coq_append ((soft a.array_default), (Tree.Coq_append
        ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x2c,
        (String.String (Coq_x20, String.EmptyString))))))), (Tree.Coq_append
        ((Tree.string_of_list soft a.array_value), (Tree.Coq_string
        (String.String (Coq_x29, String.EmptyString))))))))))

  (** val print_term :
      global_declarations -> context -> bool -> bool -> term -> Tree.t **)

  let rec print_term _UU03a3_ _UU0393_ top inapp t0 = match t0 with
  | Coq_tBox ->
    Tree.Coq_string (String.String (Coq_xe2, (String.String (Coq_x88,
      (String.String (Coq_x8e, String.EmptyString))))))
  | Coq_tRel n ->
    (match nth_error _UU0393_ n with
     | Some c ->
       let { decl_name = na; decl_body = _ } = c in
       (match na with
        | Coq_nAnon ->
          Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x41,
            (String.String (Coq_x6e, (String.String (Coq_x6f, (String.String
            (Coq_x6e, (String.String (Coq_x79, (String.String (Coq_x6d,
            (String.String (Coq_x6f, (String.String (Coq_x75, (String.String
            (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x28,
            String.EmptyString))))))))))))))))))))))), (Tree.Coq_append
            ((Tree.Coq_string (string_of_nat n)), (Tree.Coq_string
            (String.String (Coq_x29, String.EmptyString))))))
        | Coq_nNamed id -> Tree.Coq_string id)
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x52, (String.String
         (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_nat n)), (Tree.Coq_string
         (String.String (Coq_x29, String.EmptyString)))))))
  | Coq_tVar n ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x56, (String.String
      (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string n),
      (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))
  | Coq_tEvar (ev, _) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x45, (String.String
      (Coq_x76, (String.String (Coq_x61, (String.String (Coq_x72,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_nat ev)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x5b,
      (String.String (Coq_x5d, String.EmptyString))))), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))
  | Coq_tLambda (na, body) ->
    let na' = fresh_name _UU0393_ na t0 in
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x66, (String.String (Coq_x75, (String.String (Coq_x6e,
      (String.String (Coq_x20, String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_name na')), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3d,
      (String.String (Coq_x3e, (String.String (Coq_x20,
      String.EmptyString))))))))),
      (print_term _UU03a3_ ((vass na') :: _UU0393_) true false body)))))))
  | Coq_tLetIn (na, def0, body) ->
    let na' = fresh_name _UU0393_ na t0 in
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x20, String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_name na')), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3a,
      (String.String (Coq_x3d, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_append
      ((print_term _UU03a3_ _UU0393_ true false def0), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string nl),
      (print_term _UU03a3_ ((vdef na' def0) :: _UU0393_) true false body)))))))))))))
  | Coq_tApp (f, l) ->
    Tree.parens ((||) top inapp) (Tree.Coq_append
      ((print_term _UU03a3_ _UU0393_ false true f), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
      (print_term _UU03a3_ _UU0393_ false false l)))))
  | Coq_tConst c -> Tree.Coq_string (string_of_kername c)
  | Coq_tConstruct (ind, l, args) ->
    let { inductive_mind = i; inductive_ind = k } = ind in
    (match lookup_ind_decl _UU03a3_ i k with
     | Some oib ->
       (match nth_error oib.ind_ctors l with
        | Some cstr ->
          (match args with
           | [] -> Tree.Coq_string cstr.cstr_name
           | _ :: _ ->
             Tree.parens ((||) top inapp) (Tree.Coq_append ((Tree.Coq_string
               cstr.cstr_name), (Tree.Coq_append ((Tree.Coq_string
               (String.String (Coq_x5b, String.EmptyString))),
               (Tree.Coq_append
               ((Tree.print_list (print_term _UU03a3_ _UU0393_ false false)
                  (Tree.Coq_string (String.String (Coq_x20,
                  String.EmptyString))) args), (Tree.Coq_string
               (String.String (Coq_x5d, String.EmptyString))))))))))
        | None ->
          Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
            (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
            (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
            (String.String (Coq_x64, (String.String (Coq_x43, (String.String
            (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
            (String.String (Coq_x74, (String.String (Coq_x72, (String.String
            (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
            (String.String (Coq_x28,
            String.EmptyString))))))))))))))))))))))))))))))))))),
            (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
            (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
            String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
            (string_of_nat l)), (Tree.Coq_string (String.String (Coq_x29,
            String.EmptyString)))))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x43, (String.String
         (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
         (String.String (Coq_x74, (String.String (Coq_x72, (String.String
         (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
         (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))))))))))))))),
         (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat l)), (Tree.Coq_string (String.String (Coq_x29,
         String.EmptyString)))))))))))
  | Coq_tCase (indn, t1, brs) ->
    let (ind, _) = indn in
    let { inductive_mind = mind; inductive_ind = i } = ind in
    (match lookup_ind_decl _UU03a3_ mind i with
     | Some oib ->
       let print_args =
         let rec print_args _UU0393_0 nas br =
           match nas with
           | [] ->
             Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x3d,
               (String.String (Coq_x3e, String.EmptyString))))),
               (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
               String.EmptyString))), (br _UU0393_0))))
           | na :: nas0 ->
             Tree.Coq_append ((Tree.Coq_string (string_of_name na)),
               (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
               (String.String (Coq_x20, String.EmptyString))))),
               (print_args ((vass na) :: _UU0393_0) nas0 br))))
         in print_args
       in
       let brs0 =
         map (fun pat ->
           let (nas, br) = pat in
           print_args _UU0393_ (rev nas) (fun _UU0393_0 ->
             print_term _UU03a3_ _UU0393_0 true false br)) brs
       in
       let brs1 = combine brs0 oib.ind_ctors in
       Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
         (Coq_x6d, (String.String (Coq_x61, (String.String (Coq_x74,
         (String.String (Coq_x63, (String.String (Coq_x68, (String.String
         (Coq_x20, String.EmptyString))))))))))))), (Tree.Coq_append
         ((print_term _UU03a3_ _UU0393_ true false t1), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x77,
         (String.String (Coq_x69, (String.String (Coq_x74, (String.String
         (Coq_x68, (String.String (Coq_x20, String.EmptyString))))))))))))),
         (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_append
         ((Tree.print_list (fun pat ->
            let (b, cstr) = pat in
            Tree.Coq_append ((Tree.Coq_string cstr.cstr_name),
            (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
            String.EmptyString))), b)))) (Tree.Coq_append ((Tree.Coq_string
            nl), (Tree.Coq_string (String.String (Coq_x20, (String.String
            (Coq_x7c, (String.String (Coq_x20, String.EmptyString)))))))))
            brs1), (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x65, (String.String (Coq_x6e,
         (String.String (Coq_x64, String.EmptyString))))))), (Tree.Coq_string
         nl)))))))))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43,
         (String.String (Coq_x61, (String.String (Coq_x73, (String.String
         (Coq_x65, (String.String (Coq_x28, String.EmptyString))))))))))),
         (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat i)), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_term t1)), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
         (Tree.Coq_append
         ((Tree.string_of_list (fun b -> Tree.Coq_string
            (string_of_term (snd b))) brs), (Tree.Coq_string (String.String
         (Coq_x29, String.EmptyString)))))))))))))))))))
  | Coq_tProj (p, c) ->
    (match lookup_projection _UU03a3_ p with
     | Some p0 ->
       let (_, pdecl) = p0 in
       Tree.Coq_append ((print_term _UU03a3_ _UU0393_ false false c),
       (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2e,
       (String.String (Coq_x28, String.EmptyString))))), (Tree.Coq_append
       ((Tree.Coq_string pdecl), (Tree.Coq_string (String.String (Coq_x29,
       String.EmptyString))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x50, (String.String
         (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x6a,
         (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_inductive p.proj_ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat p.proj_npars)), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_nat p.proj_arg)), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
         (Tree.Coq_append ((print_term _UU03a3_ _UU0393_ true false c),
         (Tree.Coq_string (String.String (Coq_x29,
         String.EmptyString)))))))))))))))))))
  | Coq_tFix (l, n) ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x66, (String.String
      (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))), (Tree.Coq_append
      ((print_defs (print_term _UU03a3_) _UU0393_ l), (Tree.Coq_append
      ((Tree.Coq_string nl), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x69, (String.String
      (Coq_x6e, (String.String (Coq_x20, String.EmptyString))))))))),
      (Tree.Coq_string
      (nth_default (string_of_nat n)
        (map (let f0 = fun d -> d.dname in fun x -> string_of_name (f0 x)) l)
        n))))))))))
  | Coq_tCoFix (l, n) ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x63, (String.String
      (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x69,
      (String.String (Coq_x78, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))))), (Tree.Coq_append
      ((print_defs (print_term _UU03a3_) _UU0393_ l), (Tree.Coq_append
      ((Tree.Coq_string nl), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x69, (String.String
      (Coq_x6e, (String.String (Coq_x20, String.EmptyString))))))))),
      (Tree.Coq_string
      (nth_default (string_of_nat n)
        (map (let f0 = fun d -> d.dname in fun x -> string_of_name (f0 x)) l)
        n))))))))))
  | Coq_tPrim p ->
    Tree.parens top (print_prim (print_term _UU03a3_ _UU0393_ false false) p)
  | Coq_tLazy t1 ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x61, (String.String (Coq_x7a,
      (String.String (Coq_x79, (String.String (Coq_x20,
      String.EmptyString))))))))))),
      (print_term _UU03a3_ _UU0393_ false false t1)))
  | Coq_tForce t1 ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x66, (String.String (Coq_x6f, (String.String (Coq_x72,
      (String.String (Coq_x63, (String.String (Coq_x65, (String.String
      (Coq_x20, String.EmptyString))))))))))))),
      (print_term _UU03a3_ _UU0393_ false false t1)))

  (** val pr : global_declarations -> term -> Tree.t **)

  let pr _UU03a3_ t0 =
    print_term _UU03a3_ [] true false t0

  (** val print_constant_body :
      global_declarations -> kername -> constant_body -> Tree.t **)

  let print_constant_body _UU03a3_ kn = function
  | Some b ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x44, (String.String
      (Coq_x65, (String.String (Coq_x66, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x69, (String.String
      (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x6f,
      (String.String (Coq_x6e, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_kername kn)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3a,
      (String.String (Coq_x3d, (String.String (Coq_x20,
      String.EmptyString))))))))), (pr _UU03a3_ b))))))
  | None ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x41, (String.String
      (Coq_x78, (String.String (Coq_x69, (String.String (Coq_x6f,
      (String.String (Coq_x6d, (String.String (Coq_x20,
      String.EmptyString))))))))))))), (Tree.Coq_string
      (string_of_kername kn)))

  (** val pr_allowed_elim : allowed_eliminations -> String.t **)

  let pr_allowed_elim = function
  | IntoSProp ->
    String.String (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
      (String.String (Coq_x6f, (String.String (Coq_x20, (String.String
      (Coq_x73, (String.String (Coq_x70, (String.String (Coq_x72,
      (String.String (Coq_x6f, (String.String (Coq_x70,
      String.EmptyString)))))))))))))))))))
  | IntoPropSProp ->
    String.String (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
      (String.String (Coq_x6f, (String.String (Coq_x20, (String.String
      (Coq_x70, (String.String (Coq_x72, (String.String (Coq_x6f,
      (String.String (Coq_x70, (String.String (Coq_x20, (String.String
      (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x20,
      (String.String (Coq_x73, (String.String (Coq_x70, (String.String
      (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x70,
      String.EmptyString)))))))))))))))))))))))))))))))))))
  | IntoSetPropSProp ->
    String.String (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
      (String.String (Coq_x6f, (String.String (Coq_x20, (String.String
      (Coq_x73, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x2c, (String.String (Coq_x20, (String.String
      (Coq_x70, (String.String (Coq_x72, (String.String (Coq_x6f,
      (String.String (Coq_x70, (String.String (Coq_x20, (String.String
      (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x20,
      (String.String (Coq_x73, (String.String (Coq_x70, (String.String
      (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x70,
      String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))
  | IntoAny ->
    String.String (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
      (String.String (Coq_x6f, (String.String (Coq_x20, (String.String
      (Coq_x61, (String.String (Coq_x6e, (String.String (Coq_x79,
      (String.String (Coq_x20, (String.String (Coq_x73, (String.String
      (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x74,
      String.EmptyString)))))))))))))))))))))))))

  (** val print_one_inductive_body : nat -> one_inductive_body -> Tree.t **)

  let print_one_inductive_body npars body =
    let params = Tree.Coq_append ((Tree.Coq_string (string_of_nat npars)),
      (Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x70,
      (String.String (Coq_x61, (String.String (Coq_x72, (String.String
      (Coq_x61, (String.String (Coq_x6d, (String.String (Coq_x65,
      (String.String (Coq_x74, (String.String (Coq_x65, (String.String
      (Coq_x72, (String.String (Coq_x73,
      String.EmptyString))))))))))))))))))))))))
    in
    let prop =
      if body.ind_propositional
      then String.String (Coq_x70, (String.String (Coq_x72, (String.String
             (Coq_x6f, (String.String (Coq_x70, (String.String (Coq_x6f,
             (String.String (Coq_x73, (String.String (Coq_x69, (String.String
             (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x6f,
             (String.String (Coq_x6e, (String.String (Coq_x61, (String.String
             (Coq_x6c, String.EmptyString)))))))))))))))))))))))))
      else String.String (Coq_x63, (String.String (Coq_x6f, (String.String
             (Coq_x6d, (String.String (Coq_x70, (String.String (Coq_x75,
             (String.String (Coq_x74, (String.String (Coq_x61, (String.String
             (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x6f,
             (String.String (Coq_x6e, (String.String (Coq_x61, (String.String
             (Coq_x6c, String.EmptyString)))))))))))))))))))))))))
    in
    let kelim = pr_allowed_elim body.ind_kelim in
    let ctors =
      Tree.print_list (fun cstr -> Tree.Coq_append ((Tree.Coq_string
        (String.String (Coq_x7c, (String.String (Coq_x20,
        String.EmptyString))))), (Tree.Coq_append ((Tree.Coq_string
        cstr.cstr_name), (Tree.Coq_append ((Tree.Coq_string (String.String
        (Coq_x20, String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
        (string_of_nat cstr.cstr_nargs)), (Tree.Coq_string (String.String
        (Coq_x20, (String.String (Coq_x61, (String.String (Coq_x72,
        (String.String (Coq_x67, (String.String (Coq_x75, (String.String
        (Coq_x6d, (String.String (Coq_x65, (String.String (Coq_x6e,
        (String.String (Coq_x74, (String.String (Coq_x73,
        String.EmptyString))))))))))))))))))))))))))))) (Tree.Coq_string nl)
        body.ind_ctors
    in
    let projs =
      match body.ind_projs with
      | [] -> Tree.Coq_string String.EmptyString
      | _ :: _ ->
        Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_append
          ((Tree.Coq_string (String.String (Coq_x70, (String.String (Coq_x72,
          (String.String (Coq_x6f, (String.String (Coq_x6a, (String.String
          (Coq_x65, (String.String (Coq_x63, (String.String (Coq_x74,
          (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
          (Coq_x6e, (String.String (Coq_x73, (String.String (Coq_x3a,
          (String.String (Coq_x20,
          String.EmptyString))))))))))))))))))))))))))),
          (Tree.print_list (fun x -> Tree.Coq_string x) (Tree.Coq_string
            (String.String (Coq_x2c, (String.String (Coq_x20,
            String.EmptyString))))) body.ind_projs))))
    in
    Tree.Coq_append ((Tree.Coq_string body.ind_name), (Tree.Coq_append
    ((Tree.Coq_string (String.String (Coq_x28, String.EmptyString))),
    (Tree.Coq_append (params, (Tree.Coq_append ((Tree.Coq_string
    (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
    ((Tree.Coq_string prop), (Tree.Coq_append ((Tree.Coq_string
    (String.String (Coq_x2c, (String.String (Coq_x20, (String.String
    (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x69,
    (String.String (Coq_x6d, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
    (Coq_x6e, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))), (Tree.Coq_append
    ((Tree.Coq_string kelim), (Tree.Coq_append ((Tree.Coq_string
    (String.String (Coq_x29, (String.String (Coq_x20, (String.String
    (Coq_x3a, (String.String (Coq_x3d, (String.String (Coq_x20,
    String.EmptyString))))))))))), (Tree.Coq_append ((Tree.Coq_string nl),
    (Tree.Coq_append (ctors, projs)))))))))))))))))))

  (** val print_recursivity_kind : recursivity_kind -> String.t **)

  let print_recursivity_kind = function
  | Finite ->
    String.String (Coq_x49, (String.String (Coq_x6e, (String.String (Coq_x64,
      (String.String (Coq_x75, (String.String (Coq_x63, (String.String
      (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x76,
      (String.String (Coq_x65, String.EmptyString)))))))))))))))))
  | CoFinite ->
    String.String (Coq_x43, (String.String (Coq_x6f, (String.String (Coq_x49,
      (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
      (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
      (String.String (Coq_x69, (String.String (Coq_x76, (String.String
      (Coq_x65, String.EmptyString)))))))))))))))))))))
  | BiFinite ->
    String.String (Coq_x56, (String.String (Coq_x61, (String.String (Coq_x72,
      (String.String (Coq_x69, (String.String (Coq_x61, (String.String
      (Coq_x6e, (String.String (Coq_x74, String.EmptyString)))))))))))))

  (** val print_inductive_body : mutual_inductive_body -> Tree.t **)

  let print_inductive_body decl =
    Tree.Coq_append ((Tree.Coq_string
      (print_recursivity_kind decl.ind_finite)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
      (Tree.print_list (print_one_inductive_body decl.ind_npars)
        (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_string
        (String.String (Coq_x20, (String.String (Coq_x77, (String.String
        (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x68,
        (String.String (Coq_x20, String.EmptyString)))))))))))))))
        decl.ind_bodies))))

  (** val print_decl :
      global_declarations -> (kername * global_decl) -> Tree.t **)

  let print_decl _UU03a3_ = function
  | (kn, d) ->
    (match d with
     | ConstantDecl body -> print_constant_body _UU03a3_ kn body
     | InductiveDecl mind -> print_inductive_body mind)

  (** val print_global_context : global_declarations -> Tree.t **)

  let print_global_context g =
    Tree.print_list (print_decl g) (Tree.Coq_string nl) (rev g)

  (** val print_program : program -> Tree.t **)

  let print_program p =
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x45, (String.String
      (Coq_x6e, (String.String (Coq_x76, (String.String (Coq_x69,
      (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
      (Coq_x6e, (String.String (Coq_x6d, (String.String (Coq_x65,
      (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
      (Coq_x3a, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))))))))))), (Tree.Coq_append
      ((Tree.Coq_string nl), (Tree.Coq_append
      ((print_global_context (fst p)), (Tree.Coq_append ((Tree.Coq_string
      nl), (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x50,
      (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
      (Coq_x67, (String.String (Coq_x72, (String.String (Coq_x61,
      (String.String (Coq_x6d, (String.String (Coq_x3a, (String.String
      (Coq_x20, String.EmptyString))))))))))))))))))),
      (pr (fst p) (snd p)))))))))))
 end

(** val print_program : program -> String.t **)

let print_program x =
  Tree.to_string (PrintTermTree.print_program x)
