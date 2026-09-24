import LSZ.PCurvature
import LSZ.WordNilpotence

/-!
# Nilpotent Higgs bundles and flat bundles on a smooth scheme

This file adds the positive-characteristic nilpotence conditions to the
characteristic-free objects of `GeometricObjects`.  The only geometric
input is a smooth separated scheme over the field `k`; vector fields,
their restricted power, and p-curvature are the canonical constructions
from that scheme.

The LSZ convention is used on both sides: nilpotence of level at most
`p - 1` means that every word of exactly `p = ringChar k` arbitrary
contractions is zero.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] [NeZero (ringChar k)]
variable (X : LSZ.SmoothScheme k)

/-- An integrable Higgs module satisfying strong LSZ word nilpotence on
every open subset. -/
structure NilpotentHiggs extends X.IntegrableHiggs where
  nilpotent (U : X.scheme.Opens) :
    IsWordNilpotent (ringChar k)
      (fun D m ↦ toIntegrableHiggs.theta U D m)

namespace NilpotentHiggs

variable {X}

/-- Forget the word-nilpotence proof. -/
abbrev toIntegrable (E : X.NilpotentHiggs) : X.IntegrableHiggs :=
  E.toIntegrableHiggs

/-- Morphisms are morphisms of the underlying Higgs modules. -/
abbrev Hom (E F : X.NilpotentHiggs) := E.toIntegrable ⟶ F.toIntegrable

instance : Category X.NilpotentHiggs where
  Hom := Hom
  id E := 𝟙 E.toIntegrable
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forgetful functor to unrestricted integrable Higgs modules. -/
def forget : X.NilpotentHiggs ⥤ X.IntegrableHiggs where
  obj E := E.toIntegrable
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end NilpotentHiggs

/-- An integrable connection whose p-curvature satisfies strong LSZ word
nilpotence on every open subset. -/
structure NilpotentFlat extends X.IntegrableConnection where
  nilpotentPCurvature (U : X.scheme.Opens) :
    IsWordNilpotent (ringChar k)
      (fun D m ↦
        toIntegrableConnection.pCurvature U D m)

namespace NilpotentFlat

variable {X}

/-- Forget the p-curvature nilpotence proof. -/
abbrev toIntegrable (E : X.NilpotentFlat) : X.IntegrableConnection :=
  E.toIntegrableConnection

/-- Morphisms are horizontal morphisms of the underlying connections. -/
abbrev Hom (E F : X.NilpotentFlat) := E.toIntegrable ⟶ F.toIntegrable

instance : Category X.NilpotentFlat where
  Hom := Hom
  id E := 𝟙 E.toIntegrable
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forgetful functor to unrestricted integrable connections. -/
def forget : X.NilpotentFlat ⥤ X.IntegrableConnection where
  obj E := E.toIntegrable
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end NilpotentFlat

end

end LSZ.SmoothScheme
