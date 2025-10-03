open Ast0
open Datatypes
open Kernames
open List0
open Monad_utils

module GlobalEnvMap =
 struct
  type t = { env : Env.global_env; map : Env.global_decl EnvMap.EnvMap.t }

  (** val env : t -> Env.global_env **)

  let env t0 =
    t0.env

  (** val map : t -> Env.global_decl EnvMap.EnvMap.t **)

  let map t0 =
    t0.map

  (** val lookup_env : t -> kername -> Env.global_decl option **)

  let lookup_env _UU03a3_ kn =
    EnvMap.EnvMap.lookup kn _UU03a3_.map

  (** val lookup_minductive :
      t -> kername -> Env.mutual_inductive_body option **)

  let lookup_minductive _UU03a3_ kn =
    bind (Obj.magic option_monad) (Obj.magic lookup_env _UU03a3_ kn)
      (fun decl ->
      match decl with
      | Env.ConstantDecl _ -> None
      | Env.InductiveDecl mdecl -> ret (Obj.magic option_monad) mdecl)

  (** val lookup_inductive :
      t -> inductive -> (Env.mutual_inductive_body * Env.one_inductive_body)
      option **)

  let lookup_inductive _UU03a3_ kn =
    bind (Obj.magic option_monad)
      (Obj.magic lookup_minductive _UU03a3_ kn.inductive_mind) (fun mdecl ->
      bind (Obj.magic option_monad)
        (nth_error (Obj.magic Env.ind_bodies mdecl) kn.inductive_ind)
        (fun idecl -> ret (Obj.magic option_monad) (mdecl, idecl)))

  (** val lookup_constructor :
      t -> inductive -> nat ->
      ((Env.mutual_inductive_body * Env.one_inductive_body) * Env.constructor_body)
      option **)

  let lookup_constructor _UU03a3_ kn c =
    bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ kn)
      (fun x ->
      let (mdecl, idecl) = x in
      bind (Obj.magic option_monad)
        (nth_error (Obj.magic Env.ind_ctors idecl) c) (fun cdecl ->
        ret (Obj.magic option_monad) ((mdecl, idecl), cdecl)))

  (** val make : Env.global_env -> t **)

  let make g =
    { env = g; map = (EnvMap.EnvMap.of_global_env (Env.declarations g)) }
 end
