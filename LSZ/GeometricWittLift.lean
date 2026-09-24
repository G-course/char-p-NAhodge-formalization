import LSZ.AbsoluteFrobenius
import LSZ.WittLift

/-!
# Scheme-theoretic `W₂` lifts and Frobenius lifts

This file gives the geometric input used by the scheme-level LSZ
construction.  The characteristic-`p` scheme is already bundled as a
`SmoothScheme k`; consequently its structure morphism and smoothness are
not repeated in the lifting data.

A Frobenius lift contains only the lifted endomorphism and the two
properties that make it a Frobenius lift.  Its endomorphism on the special
fibre is constructed from the pullback universal property rather than
being supplied as additional data.
-/

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable (X : LSZ.SmoothScheme k)

/-- A smooth `W₂(k)`-lift of the already fixed smooth `k`-scheme `X`.

The special-fibre isomorphism is required to respect the fixed structure
map of `X`; no second structure map or smoothness proof for `X` occurs in
this record. -/
structure W₂Lift where
  lift : AlgebraicGeometry.Scheme.{u}
  structureMap : lift ⟶ AlgebraicGeometry.Spec (.of (LSZ.W₂ p k))
  smooth : AlgebraicGeometry.Smooth structureMap
  specialFiberIso :
    pullback structureMap (LSZ.specialFiberPoint p k) ≅ X.scheme
  specialFiberIso_over :
    specialFiberIso.hom ≫ X.structureMap = pullback.snd _ _

namespace W₂Lift

variable {X}

/-- The scheme-theoretic special fibre of a fixed lift. -/
abbrev specialFiber (L : X.W₂Lift (p := p)) :
    AlgebraicGeometry.Scheme.{u} :=
  pullback L.structureMap (LSZ.specialFiberPoint p k)

attribute [instance] W₂Lift.smooth

end W₂Lift

/-- A Frobenius lift of `X` on a fixed `W₂(k)`-lift.

The first equation says that `liftFrob` is semilinear for Witt Frobenius.
The second says that its reduction, transported through the fixed
special-fibre identification, is the absolute Frobenius of `X`.
-/
structure FrobeniusLift (L : X.W₂Lift (p := p)) where
  liftFrob : L.lift ⟶ L.lift
  liftFrob_over :
    liftFrob ≫ L.structureMap =
      L.structureMap ≫ LSZ.w₂FrobeniusSpec p k
  reduction_eq :
    L.specialFiberIso.inv ≫
        pullback.lift
          (pullback.fst L.structureMap (LSZ.specialFiberPoint p k) ≫ liftFrob)
          (pullback.snd L.structureMap (LSZ.specialFiberPoint p k) ≫
            LSZ.fieldFrobeniusSpec p k)
          (by
            rw [Category.assoc, liftFrob_over]
            rw [← Category.assoc (pullback.fst _ _) L.structureMap]
            rw [pullback.condition]
            rw [Category.assoc, Category.assoc,
              LSZ.specialFiberPoint_frobenius]) ≫
        L.specialFiberIso.hom =
      AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X.scheme

namespace FrobeniusLift

variable {X} {L : X.W₂Lift (p := p)}

/-- The reduction of a lifted Frobenius, constructed by the pullback
universal property. -/
def specialFiberMap (Phi : X.FrobeniusLift L) :
    L.specialFiber ⟶ L.specialFiber :=
  pullback.lift
    (pullback.fst L.structureMap (LSZ.specialFiberPoint p k) ≫ Phi.liftFrob)
    (pullback.snd L.structureMap (LSZ.specialFiberPoint p k) ≫
      LSZ.fieldFrobeniusSpec p k)
    (by
      rw [Category.assoc, Phi.liftFrob_over]
      rw [← Category.assoc (pullback.fst _ _) L.structureMap]
      rw [pullback.condition]
      rw [Category.assoc, Category.assoc,
        LSZ.specialFiberPoint_frobenius])

@[reassoc (attr := simp)]
lemma specialFiberMap_fst (Phi : X.FrobeniusLift L) :
    Phi.specialFiberMap ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Phi.liftFrob := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma specialFiberMap_snd (Phi : X.FrobeniusLift L) :
    Phi.specialFiberMap ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ LSZ.fieldFrobeniusSpec p k := by
  exact pullback.lift_snd _ _ _

/-- By definition, the constructed special-fibre map is the absolute
Frobenius after transport to `X`. -/
lemma reduction_eq_absoluteFrobenius (Phi : X.FrobeniusLift L) :
    L.specialFiberIso.inv ≫ Phi.specialFiberMap ≫
        L.specialFiberIso.hom =
      AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X.scheme :=
  Phi.reduction_eq

/-- Compatibility bridge to the older scheme-level interfaces.  It adds no
new mathematical data: the repeated structure map and the special-fibre
map are filled by the constructions above. -/
def toLegacyW₂Lift (L : X.W₂Lift (p := p)) :
    LSZ.W₂Lift (p := p) (k := k) X.scheme where
  structureMap := X.structureMap
  smooth := X.smooth
  lift := L.lift
  liftStructureMap := L.structureMap
  liftSmooth := L.smooth
  specialFiberIso := L.specialFiberIso
  specialFiberIso_over := L.specialFiberIso_over

/-- A genuine geometric Frobenius lift supplies the legacy global-lift
interface with absolute Frobenius, rather than an arbitrary endomorphism. -/
def toLegacy (Phi : X.FrobeniusLift L) :
    LSZ.GlobalFrobeniusLift X.scheme (toLegacyW₂Lift L) where
  frobenius := AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X.scheme
  liftFrob := Phi.liftFrob
  liftFrob_over := Phi.liftFrob_over
  specialFiberMap := Phi.specialFiberMap
  specialFiberMap_fst := Phi.specialFiberMap_fst
  specialFiberMap_snd := Phi.specialFiberMap_snd
  reduction_eq := Phi.reduction_eq_absoluteFrobenius

end FrobeniusLift

end

end LSZ.SmoothScheme
