open All_Forall
open Ascii
open BasicAst
open Byte
open CRelationClasses
open Classes0
open Datatypes
open EAst
open Erasure
open ErasureFunction
open ExAst
open Kernames
open MCProd
open Optimize
open PCUICAst
open PCUICAstUtils
open PCUICWfEnv
open PCUICWfEnvImpl
open Primitive
open ResultMonad
open Signature
open Specif
open String0
open Universes0
open Utils
open Bytestring
open Config0
open Monad_utils

type __ = Obj.t

module PEnv = PCUICEnvironment

(** val compute_masks :
    (kername -> bitmask option) -> bool -> bool -> global_env -> (dearg_set,
    String.t) result **)

let compute_masks overridden_masks do_trim_const_masks do_trim_ctor_masks _UU03a3_ =
  let { const_masks = const_masks0; ind_masks = ind_masks0 } =
    timed (String ((Ascii (false, false, true, false, false, false, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, true, false, false, true, true, true,
      false)), (String ((Ascii (true, true, true, false, false, true, true,
      false)), (String ((Ascii (false, false, false, false, false, true,
      false, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, true, true, true, false,
      true, true, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, true, false,
      true, true, false)), (String ((Ascii (true, false, false, true, true,
      true, true, false)), (String ((Ascii (true, true, false, false, true,
      true, true, false)), (String ((Ascii (true, false, false, true, false,
      true, true, false)), (String ((Ascii (true, true, false, false, true,
      true, true, false)), EmptyString)))))))))))))))))))))))))))) (fun _ ->
      analyze_env overridden_masks _UU03a3_)
  in
  let const_masks1 =
    if do_trim_const_masks
    then trim_const_masks const_masks0
    else Obj.magic id const_masks0
  in
  let ind_masks1 =
    if do_trim_ctor_masks
    then trim_ind_masks ind_masks0
    else Obj.magic id ind_masks0
  in
  bind (Obj.magic coq_Monad_result)
    (Obj.magic throwIf
      (negb (is_expanded_env ind_masks1 const_masks1 _UU03a3_))
      (String.String (Coq_x45, (String.String (Coq_x72, (String.String
      (Coq_x61, (String.String (Coq_x73, (String.String (Coq_x65,
      (String.String (Coq_x64, (String.String (Coq_x20, (String.String
      (Coq_x65, (String.String (Coq_x6e, (String.String (Coq_x76,
      (String.String (Coq_x69, (String.String (Coq_x72, (String.String
      (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x6d,
      (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
      (Coq_x74, (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x73, (String.String (Coq_x20, (String.String
      (Coq_x6e, (String.String (Coq_x6f, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x65, (String.String
      (Coq_x78, (String.String (Coq_x70, (String.String (Coq_x61,
      (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
      (Coq_x65, (String.String (Coq_x64, (String.String (Coq_x20,
      (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
      (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x67,
      (String.String (Coq_x68, (String.String (Coq_x20, (String.String
      (Coq_x66, (String.String (Coq_x6f, (String.String (Coq_x72,
      (String.String (Coq_x20, (String.String (Coq_x64, (String.String
      (Coq_x65, (String.String (Coq_x61, (String.String (Coq_x72,
      (String.String (Coq_x67, (String.String (Coq_x69, (String.String
      (Coq_x6e, (String.String (Coq_x67, (String.String (Coq_x20,
      (String.String (Coq_x74, (String.String (Coq_x6f, (String.String
      (Coq_x20, (String.String (Coq_x62, (String.String (Coq_x65,
      (String.String (Coq_x20, (String.String (Coq_x70, (String.String
      (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x76,
      (String.String (Coq_x61, (String.String (Coq_x62, (String.String
      (Coq_x6c, (String.String (Coq_x79, (String.String (Coq_x20,
      (String.String (Coq_x63, (String.String (Coq_x6f, (String.String
      (Coq_x72, (String.String (Coq_x72, (String.String (Coq_x65,
      (String.String (Coq_x63, (String.String (Coq_x74,
      String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (fun _ ->
    bind (Obj.magic coq_Monad_result)
      (Obj.magic throwIf
        (negb (valid_masks_env ind_masks1 const_masks1 _UU03a3_))
        (String.String (Coq_x41, (String.String (Coq_x6e, (String.String
        (Coq_x61, (String.String (Coq_x6c, (String.String (Coq_x79,
        (String.String (Coq_x73, (String.String (Coq_x69, (String.String
        (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x70,
        (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
        (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
        (String.String (Coq_x65, (String.String (Coq_x64, (String.String
        (Coq_x20, (String.String (Coq_x6d, (String.String (Coq_x61,
        (String.String (Coq_x73, (String.String (Coq_x6b, (String.String
        (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x74,
        (String.String (Coq_x68, (String.String (Coq_x61, (String.String
        (Coq_x74, (String.String (Coq_x20, (String.String (Coq_x61,
        (String.String (Coq_x73, (String.String (Coq_x6b, (String.String
        (Coq_x20, (String.String (Coq_x74, (String.String (Coq_x6f,
        (String.String (Coq_x20, (String.String (Coq_x72, (String.String
        (Coq_x65, (String.String (Coq_x6d, (String.String (Coq_x6f,
        (String.String (Coq_x76, (String.String (Coq_x65, (String.String
        (Coq_x20, (String.String (Coq_x6c, (String.String (Coq_x69,
        (String.String (Coq_x76, (String.String (Coq_x65, (String.String
        (Coq_x20, (String.String (Coq_x61, (String.String (Coq_x72,
        (String.String (Coq_x67, (String.String (Coq_x75, (String.String
        (Coq_x6d, (String.String (Coq_x65, (String.String (Coq_x6e,
        (String.String (Coq_x74, (String.String (Coq_x73,
        String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (fun _ -> Ok { const_masks = const_masks1; ind_masks = ind_masks1 }))

(** val make_env : PCUICEnvironment.global_env_ext -> __ **)

let make_env _UU03a3_ =
  abstract_make_wf_env_ext extraction_checker_flags
    (optimized_abstract_env_impl extraction_checker_flags
      fake_guard_impl_instance)
    (Obj.magic build_wf_env_from_env extraction_checker_flags
      (fst_ctx _UU03a3_)) (snd _UU03a3_)

(** val erase_term : PCUICEnvironment.global_env_ext -> term -> EAst.term **)

let erase_term _UU03a3_ t0 =
  let wfext = make_env _UU03a3_ in
  erase
    (optimized_abstract_env_impl extraction_checker_flags
      fake_guard_impl_instance) wfext [] t0
