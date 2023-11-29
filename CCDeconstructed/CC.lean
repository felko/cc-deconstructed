inductive CC :=
  | cc0 | cc1 | cc2 | cc3
  deriving Repr, DecidableEq

inductive Feature :=
  | sealed_type_parameters
  | box_type
  | type_bindings
  | explicit_boxing
  deriving Repr

open Feature

class inductive HasFeature : CC → Feature → Prop :=
  | cc0_has_box_type               : HasFeature cc0 box_type
  | cc0_has_explicit_boxing        : HasFeature cc0 explicit_boxicc

  | cc1_has_box_type               : HasFeature cc1 box_type
  | cc1_has_explicit_boxing        : HasFeature cc1 explicit_boxing
  | cc1_has_sealed_type_parameters : HasFeature cc1 sealed_type_parametecc

  | cc2_has_explicit_boxing        : HasFeature cc2 explicit_boxing
  | cc2_has_sealed_type_parameters : HasFeature cc2 sealed_type_parameters
  | cc2_has_type_bindings          : HasFeature cc2 type_bindincc

  | cc3_has_sealed_type_parameters : HasFeature cc3 sealed_type_parameters
  | cc3_has_type_bindings          : HasFeature cc3 type_bindings
  deriving Repr

attribute [instance]
  HasFeature.cc0_has_box_type
  HasFeature.cc0_has_explicit_boxing
  HasFeature.cc1_has_box_type
  HasFeature.cc1_has_explicit_boxing
  HasFeature.cc1_has_sealed_type_parameters
  HasFeature.cc2_has_explicit_boxing
  HasFeature.cc2_has_sealed_type_parameters
  HasFeature.cc2_has_type_bindings
  HasFeature.cc3_has_sealed_type_parameters
  HasFeature.cc3_has_type_bindings

class Embed.{u} (i : CC) (j : CC) (F : CC → Sort u) :=
  embed : F i → F j

notation:0 "⟦" t:0 "⟧" => Embed.embed t
