open BasicAst
open Datatypes
open EAst
open Kernames
open List0
open Monad_utils

module GlobalContextMap =
 struct
  type t = { global_decls : global_declarations;
             map : global_decl EnvMap.EnvMap.t }

  (** val global_decls : t -> global_declarations **)

  let global_decls t0 =
    t0.global_decls

  (** val map : t -> global_decl EnvMap.EnvMap.t **)

  let map t0 =
    t0.map

  (** val lookup_env : t -> kername -> global_decl option **)

  let lookup_env _UU03a3_ kn =
    EnvMap.EnvMap.lookup kn _UU03a3_.map

  (** val lookup_minductive : t -> kername -> mutual_inductive_body option **)

  let lookup_minductive _UU03a3_ kn =
    bind (Obj.magic option_monad) (Obj.magic lookup_env _UU03a3_ kn)
      (fun decl ->
      match decl with
      | ConstantDecl _ -> None
      | InductiveDecl mdecl -> ret (Obj.magic option_monad) mdecl)

  (** val lookup_inductive :
      t -> inductive -> (mutual_inductive_body * one_inductive_body) option **)

  let lookup_inductive _UU03a3_ kn =
    bind (Obj.magic option_monad)
      (Obj.magic lookup_minductive _UU03a3_ kn.inductive_mind) (fun mdecl ->
      bind (Obj.magic option_monad)
        (nth_error (Obj.magic mdecl.ind_bodies) kn.inductive_ind)
        (fun idecl -> ret (Obj.magic option_monad) (mdecl, idecl)))

  (** val lookup_constructor :
      t -> inductive -> nat ->
      ((mutual_inductive_body * one_inductive_body) * constructor_body) option **)

  let lookup_constructor _UU03a3_ kn c =
    bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ kn)
      (fun x ->
      let (mdecl, idecl) = x in
      bind (Obj.magic option_monad) (nth_error (Obj.magic idecl.ind_ctors) c)
        (fun cdecl -> ret (Obj.magic option_monad) ((mdecl, idecl), cdecl)))

  (** val lookup_projection :
      t -> projection ->
      (((mutual_inductive_body * one_inductive_body) * constructor_body) * projection_body)
      option **)

  let lookup_projection _UU03a3_ p =
    bind (Obj.magic option_monad)
      (Obj.magic lookup_constructor _UU03a3_ p.proj_ind O) (fun x ->
      let (y, cdecl) = x in
      let (mdecl, idecl) = y in
      bind (Obj.magic option_monad)
        (nth_error (Obj.magic idecl.ind_projs) p.proj_arg) (fun pdecl ->
        ret (Obj.magic option_monad) (((mdecl, idecl), cdecl), pdecl)))

  (** val lookup_inductive_pars : t -> kername -> nat option **)

  let lookup_inductive_pars _UU03a3_ kn =
    bind (Obj.magic option_monad) (Obj.magic lookup_minductive _UU03a3_ kn)
      (fun mdecl -> ret (Obj.magic option_monad) mdecl.ind_npars)

  (** val lookup_inductive_kind : t -> kername -> recursivity_kind option **)

  let lookup_inductive_kind _UU03a3_ kn =
    bind (Obj.magic option_monad) (Obj.magic lookup_minductive _UU03a3_ kn)
      (fun mdecl -> ret (Obj.magic option_monad) mdecl.ind_finite)

  (** val inductive_isprop_and_pars :
      t -> inductive -> (bool * nat) option **)

  let inductive_isprop_and_pars _UU03a3_ ind =
    bind (Obj.magic option_monad) (Obj.magic lookup_inductive _UU03a3_ ind)
      (fun x ->
      let (mdecl, idecl) = x in
      ret (Obj.magic option_monad) (idecl.ind_propositional, mdecl.ind_npars))

  (** val lookup_constructor_pars_args :
      t -> inductive -> nat -> (nat * nat) option **)

  let lookup_constructor_pars_args _UU03a3_ ind c =
    bind (Obj.magic option_monad)
      (Obj.magic lookup_constructor _UU03a3_ ind c) (fun x ->
      let (y, cdecl) = x in
      let (mdecl, _) = y in
      ret (Obj.magic option_monad) (mdecl.ind_npars, cdecl.cstr_nargs))

  (** val make : global_declarations -> t **)

  let make g =
    { global_decls = g; map = (EnvMap.EnvMap.of_global_env g) }
 end
