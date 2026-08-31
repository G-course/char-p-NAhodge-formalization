import LSZ.FilteredColimitTensor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-!
# Stalks and tensor products of module presheaves

The comparison is obtained by applying the varying-base filtered-colimit
theorem to the neighbourhood category of a point.  Its module structures are
definitionally the stalk module structures from mathlib.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open scoped MonoidalCategory TensorProduct

namespace LSZ.StalkTensor

universe u

noncomputable section

variable {X : TopCat.{u}}

private abbrev neighborhoodRing
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (OpenNhds.inclusion x).op ⋙ R

private noncomputable abbrev neighborhoodModule
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    (Q : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u}
      (neighborhoodRing R x ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward₀OfCommRingCat
    (OpenNhds.inclusion x) R).obj Q

/-- A stalk of a module presheaf, regarded as a module over the stalk of the
ring presheaf. -/
noncomputable def stalkObj
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    (Q : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)) :
    ModuleCat (R.stalk x) :=
  ModuleCat.of _ (TopCat.Presheaf.stalk (C := Ab.{u}) Q.presheaf x)

/-- The stalk of an objectwise tensor product is the tensor product of the
two stalks. -/
noncomputable def tensorIso
    (R : X.Presheaf CommRingCat.{u})
    (M N : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    stalkObj R x (M ⊗ N) ≅ stalkObj R x M ⊗ stalkObj R x N := by
  exact FilteredColimitTensor.tensorIso
    (neighborhoodRing R x)
    (neighborhoodModule R x M) (neighborhoodModule R x N)

/-- Formula for the stalk tensor comparison on germs of local sections. -/
@[simp]
lemma tensorIso_hom_germ_tmul
    (R : X.Presheaf CommRingCat.{u})
    (M N : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    (tensorIso R M N x).hom
        (TopCat.Presheaf.germ (C := Ab.{u}) (M ⊗ N).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n)) =
      TopCat.Presheaf.germ (C := Ab.{u}) M.presheaf U x hx m ⊗ₜ[R.stalk x]
        TopCat.Presheaf.germ (C := Ab.{u}) N.presheaf U x hx n := by
  exact FilteredColimitTensor.tensorIso_hom_inclusion_tmul
    (neighborhoodRing R x)
    (neighborhoodModule R x M) (neighborhoodModule R x N)
    (op ⟨U, hx⟩) m n

/-- A morphism of module presheaves induces the corresponding linear map on
stalks. -/
noncomputable def map
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    {P Q : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q) :
    stalkObj R x P ⟶ stalkObj R x Q :=
  FilteredColimitTensor.colimitMap (neighborhoodRing R x)
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (OpenNhds.inclusion x) R).map f)

/-- Formula for the induced linear map on a germ. -/
@[simp]
lemma map_germ
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    {P Q : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    map R x f (TopCat.Presheaf.germ (C := Ab.{u}) P.presheaf U x hx m) =
      TopCat.Presheaf.germ (C := Ab.{u}) Q.presheaf U x hx
        (f.app (op U) m) := by
  exact FilteredColimitTensor.colimitMap_inclusion
    (neighborhoodRing R x)
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (OpenNhds.inclusion x) R).map f)
    (op ⟨U, hx⟩) m

/-- Naturality of the stalk tensor comparison. -/
lemma tensorIso_naturality
    (R : X.Presheaf CommRingCat.{u}) (x : X)
    {M M' N N' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    map R x (f ⊗ₘ g) ≫ (tensorIso R M' N' x).hom =
      (tensorIso R M N x).hom ≫
        (map R x f ⊗ₘ map R x g) := by
  exact FilteredColimitTensor.tensorIso_naturality
    (neighborhoodRing R x)
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (OpenNhds.inclusion x) R).map f)
    ((PresheafOfModules.pushforward₀OfCommRingCat
      (OpenNhds.inclusion x) R).map g)

end

end LSZ.StalkTensor
