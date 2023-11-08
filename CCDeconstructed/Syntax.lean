import CCDeconstructed.CC
import CCDeconstructed.Var

open VarCat Feature

section Syntax
  variable (i : CC)

  abbrev Cap := Finset (Var (var i))

  inductive TypevarKind where
    | ε : TypevarKind
    | sealed [HasFeature i sealed_type_parameters] : TypevarKind

  inductive Typ where
    | top : Typ
    | var : Var (tvar i) -> Typ
    | arr : Typ -> Typ -> Typ
    | all : TypevarKind i -> Typ -> Typ -> Typ
    | box [HasFeature i .box_type] : Typ -> Typ
    | cap : Typ -> Cap i -> Typ

  inductive Exp where
    | var : Var (var i) -> Exp
    | abs : Typ i -> Exp -> Exp
    | app : Var (var i) -> Var (var i) -> Exp
    | tabs : Typ i -> Exp -> Exp
    | tapp : Var (var i) -> Typ i -> Exp
    | let : Exp -> Exp -> Exp
    | type [HasFeature i type_bindings] : Typ i -> Exp -> Exp
    | box [HasFeature i explicit_boxing] : Var (var i) -> Exp
    | unbox [HasFeature i explicit_boxing] : Var (var i) -> Exp
end Syntax
