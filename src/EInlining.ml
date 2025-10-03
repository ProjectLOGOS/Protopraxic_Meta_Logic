open Byte
open Datatypes
open EAst
open EPrimitive
open EWcbvEval
open EWellformed
open Kernames
open List0
open MCList
open MCProd
open Bytestring

type inlining = KernameSet.t

type constants_inlining = term KernameMap.t

(** val inline : constants_inlining -> term -> term **)

let rec inline inlining0 = function
| Coq_tEvar (n, l) -> Coq_tEvar (n, (map (inline inlining0) l))
| Coq_tLambda (na, t1) -> Coq_tLambda (na, (inline inlining0 t1))
| Coq_tLetIn (na, b, t1) ->
  Coq_tLetIn (na, (inline inlining0 b), (inline inlining0 t1))
| Coq_tApp (u, v) -> Coq_tApp ((inline inlining0 u), (inline inlining0 v))
| Coq_tConst k ->
  (match KernameMap.find k inlining0 with
   | Some t1 -> t1
   | None -> Coq_tConst k)
| Coq_tConstruct (ind, n, args) ->
  Coq_tConstruct (ind, n, (map (inline inlining0) args))
| Coq_tCase (indn, c, brs) ->
  Coq_tCase (indn, c, (map (on_snd (inline inlining0)) brs))
| Coq_tProj (p, c) -> Coq_tProj (p, (inline inlining0 c))
| Coq_tFix (mfix, idx) ->
  Coq_tFix ((map (map_def (inline inlining0)) mfix), idx)
| Coq_tCoFix (mfix, idx) ->
  Coq_tCoFix ((map (map_def (inline inlining0)) mfix), idx)
| Coq_tPrim prim -> Coq_tPrim (map_prim (inline inlining0) prim)
| Coq_tLazy t1 -> Coq_tLazy (inline inlining0 t1)
| Coq_tForce t1 -> Coq_tForce (inline inlining0 t1)
| x -> x

(** val inline_constant_decl :
    constants_inlining -> constant_body -> constant_body **)

let inline_constant_decl inlining0 cb =
  option_map (inline inlining0) cb

(** val inline_decl :
    constants_inlining -> (kername * global_decl) -> kername * global_decl **)

let inline_decl inlining0 d =
  match snd d with
  | ConstantDecl cb ->
    ((fst d), (ConstantDecl (inline_constant_decl inlining0 cb)))
  | InductiveDecl _ -> d

(** val inline_add :
    inlining -> (global_declarations * constants_inlining) ->
    (KernameSet.elt * global_decl) -> term KernameMap.t **)

let inline_add inlining0 acc decl =
  let (_, inls) = acc in
  if KernameSet.mem (fst decl) inlining0
  then (match snd decl with
        | ConstantDecl c ->
          (match c with
           | Some body -> KernameMap.add (fst decl) body inls
           | None -> inls)
        | InductiveDecl _ -> inls)
  else inls

(** val inline_env :
    KernameSet.t -> (kername * global_decl) list ->
    global_declarations * constants_inlining **)

let inline_env inlining0 _UU03a3_ =
  let inline_decl0 = fun pat decl ->
    let (_UU03a3_0, inls) = pat in
    let inldecl = inline_decl inls decl in
    ((inldecl :: _UU03a3_0), (inline_add inlining0 (_UU03a3_0, inls) inldecl))
  in
  fold_left inline_decl0 (rev _UU03a3_) ([], KernameMap.empty)

type inlined_program = (global_declarations * constants_inlining) * term

(** val inline_program : KernameSet.t -> program -> inlined_program **)

let inline_program inlining0 p =
  let (_UU03a3_', inls) = inline_env inlining0 (fst p) in
  ((_UU03a3_', inls), (inline inls (snd p)))

(** val inline_transformation :
    coq_EEnvFlags -> coq_WcbvFlags -> KernameSet.t -> (global_declarations,
    global_declarations * constants_inlining, term, term, term, term)
    Transform.Transform.t **)

let inline_transformation _ _ inlining0 =
  { Transform.Transform.name = (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x6c, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x67, (String.String (Coq_x20,
    String.EmptyString)))))))))))))))))); Transform.Transform.transform =
    (fun p _ -> inline_program inlining0 p) }

(** val forget_inlining_info_transformation :
    coq_EEnvFlags -> coq_WcbvFlags ->
    (global_declarations * constants_inlining, global_declarations, term,
    term, term, term) Transform.Transform.t **)

let forget_inlining_info_transformation _ _ =
  { Transform.Transform.name = (String.String (Coq_x66, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x67,
    (String.String (Coq_x65, (String.String (Coq_x74, (String.String
    (Coq_x74, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x67, (String.String (Coq_x20, (String.String
    (Coq_x61, (String.String (Coq_x62, (String.String (Coq_x6f,
    (String.String (Coq_x75, (String.String (Coq_x74, (String.String
    (Coq_x20, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x6c, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x67, (String.String (Coq_x20, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x66,
    (String.String (Coq_x6f,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ -> ((fst (fst p)), (snd p))) }
