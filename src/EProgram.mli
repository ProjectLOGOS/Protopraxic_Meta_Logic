open Datatypes
open EAst
open EEnvMap
open Kernames
open Bytestring

type inductive_mapping = inductive * (String.t * nat list)

type inductives_mapping = inductive_mapping list

type eprogram = global_declarations * term

type eprogram_env = GlobalContextMap.t * term
