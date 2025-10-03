open Datatypes
open ErasureFunction
open Extract
open Kernames
open PCUICAst
open PCUICWfEnv
open Specif
open Config0

type __ = Obj.t

val erase_global_deps_fast :
  KernameSet.t -> (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT)
  sigT -> __ -> PCUICEnvironment.global_declarations ->
  E.global_declarations * KernameSet.t

val erase_global_fast :
  (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT) sigT ->
  KernameSet.t -> __ -> PCUICEnvironment.global_declarations ->
  E.global_declarations * KernameSet.t
