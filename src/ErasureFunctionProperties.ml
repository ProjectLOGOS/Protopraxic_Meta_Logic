open Datatypes
open ErasureFunction
open Extract
open Kernames
open PCUICAst
open PCUICWfEnv
open Specif
open Config0

type __ = Obj.t

(** val erase_global_deps_fast :
    KernameSet.t -> (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT)
    sigT -> __ -> PCUICEnvironment.global_declarations ->
    E.global_declarations * KernameSet.t **)

let rec erase_global_deps_fast deps x_type x = function
| [] -> ([], deps)
| p :: decls0 ->
  let (kn, g) = p in
  (match g with
   | PCUICEnvironment.ConstantDecl cb ->
     if KernameSet.mem kn deps
     then let xext' =
            abstract_make_wf_env_ext extraction_checker_flags x_type x
              (PCUICEnvironment.cst_universes cb)
          in
          let cb' = erase_constant_body x_type xext' cb in
          let deps0 = KernameSet.union deps (snd cb') in
          let _UU03a3_' = erase_global_deps_fast deps0 x_type x decls0 in
          (((kn, (E.ConstantDecl (fst cb'))) :: (fst _UU03a3_')),
          (snd _UU03a3_'))
     else erase_global_deps_fast deps x_type x decls0
   | PCUICEnvironment.InductiveDecl mib ->
     if KernameSet.mem kn deps
     then let mib' = erase_mutual_inductive_body mib in
          let _UU03a3_' = erase_global_deps_fast deps x_type x decls0 in
          (((kn, (E.InductiveDecl mib')) :: (fst _UU03a3_')), (snd _UU03a3_'))
     else erase_global_deps_fast deps x_type x decls0)

(** val erase_global_fast :
    (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT) sigT ->
    KernameSet.t -> __ -> PCUICEnvironment.global_declarations ->
    E.global_declarations * KernameSet.t **)

let erase_global_fast x_type deps x decls =
  erase_global_deps_fast deps x_type x decls
