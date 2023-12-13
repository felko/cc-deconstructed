import CCDeconstructed.CC
import CCDeconstructed.Var

import Mathlib.Data.List.AList

open VarCat Feature

abbrev Cap (i : CC) := Finset (Var (var i))

inductive TypevarKind (i : CC) where
  | ε : TypevarKind i
  | sealed [HasFeature i sealed_type_parameters] : TypevarKind i
  deriving DecidableEq

inductive Typ (i : CC) where
  | top : Typ i
  | var : Var (tvar i) → Typ i
  | arr : Typ i → Typ i → Typ i
  | all : TypevarKind i → Typ i → Typ i → Typ i
  | box [HasFeature i .box_type] : Typ i → Typ i
  | cap : Typ i → Cap i → Typ i
  deriving DecidableEq

inductive Exp (i : CC) where
  | var : Var (var i) → Exp i
  | abs : Typ i → Exp i → Exp i
  | app : Var (var i) → Var (var i) → Exp i
  | tabs : TypevarKind i → Typ i → Exp i → Exp i
  | tapp : Var (var i) → Typ i → Exp i
  | let_ : Exp i → Exp i → Exp i
  | type [HasFeature i type_bindings] : Typ i → Exp i → Exp i
  | box [HasFeature i explicit_boxing] : Var (var i) → Exp i
  | unbox [HasFeature i explicit_boxing] : Var (var i) → Exp i
  deriving DecidableEq
