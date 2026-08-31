import LSZ.WittLift
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Affine Frobenius atlases on a fixed `W₂(k)`-lifting

This file contains the geometric choice used in the Lan--Sheng--Zuo
construction.  The cover is a cover of the one special-fibre scheme `X`;
there is no second scheme called `X'`.

For every affine member `Uᵢ ⟶ X` we choose an open affine lifting
`Ũᵢ ⟶ X̃` and a Frobenius lifting on `Ũᵢ`.  Its reduction is required to
be the restriction of one fixed Frobenius endomorphism `F : X ⟶ X`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace LSZ

universe u

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {X : AlgebraicGeometry.Scheme.{u}}

namespace LocalFrobeniusLift

/-- The special fibre of a lifted open chart `Ũ ⟶ X̃`. -/
noncomputable abbrev specialFiber
    (L : W₂Lift (p := p) (k := k) X)
    {Y : AlgebraicGeometry.Scheme.{u}} (j : Y ⟶ L.lift) :
    AlgebraicGeometry.Scheme.{u} :=
  pullback (j ≫ L.liftStructureMap) (specialFiberPoint p k)

/-- The canonical map from the special fibre of a lifted chart to the
special fibre of the total lifting. -/
noncomputable def toTotalSpecialFiber
    (L : W₂Lift (p := p) (k := k) X)
    {Y : AlgebraicGeometry.Scheme.{u}} (j : Y ⟶ L.lift) :
    specialFiber L j ⟶ L.specialFiber :=
  pullback.lift
    (pullback.fst (j ≫ L.liftStructureMap) (specialFiberPoint p k) ≫ j)
    (pullback.snd (j ≫ L.liftStructureMap) (specialFiberPoint p k))
    (by
      rw [Category.assoc]
      exact pullback.condition)

omit [CharP k p] in
@[reassoc (attr := simp)]
lemma toTotalSpecialFiber_fst
    (L : W₂Lift (p := p) (k := k) X)
    {Y : AlgebraicGeometry.Scheme.{u}} (j : Y ⟶ L.lift) :
    toTotalSpecialFiber L j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ j := by
  unfold toTotalSpecialFiber
  exact pullback.lift_fst _ _ _

omit [CharP k p] in
@[reassoc (attr := simp)]
lemma toTotalSpecialFiber_snd
    (L : W₂Lift (p := p) (k := k) X)
    {Y : AlgebraicGeometry.Scheme.{u}} (j : Y ⟶ L.lift) :
    toTotalSpecialFiber L j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold toTotalSpecialFiber
  exact pullback.lift_snd _ _ _

end LocalFrobeniusLift

/-- A Frobenius lifting on one affine member `j : U ⟶ X` of a cover.

The chart `lift` is an affine open subscheme of the fixed total lifting.
`specialFiberIso` identifies its actual scheme-theoretic special fibre with
`U`, compatibly with `j`.  The last four fields say that `liftFrob` is
Witt-Frobenius semilinear and reduces to the local Frobenius on `U`.
-/
structure LocalFrobeniusLift
    (L : W₂Lift (p := p) (k := k) X)
    {U : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (F : X ⟶ X) where
  lift : AlgebraicGeometry.Scheme.{u}
  liftToTotal : lift ⟶ L.lift
  liftToTotal_open : AlgebraicGeometry.IsOpenImmersion liftToTotal
  lift_affine : AlgebraicGeometry.IsAffine lift

  specialFiberIso :
    LocalFrobeniusLift.specialFiber L liftToTotal ≅ U
  specialFiberIso_toX :
    specialFiberIso.hom ≫ j =
      LocalFrobeniusLift.toTotalSpecialFiber L liftToTotal ≫
        L.specialFiberIso.hom

  frobenius : U ⟶ U
  frobenius_toX : frobenius ≫ j = j ≫ F

  liftFrob : lift ⟶ lift
  liftFrob_over :
    liftFrob ≫ liftToTotal ≫ L.liftStructureMap =
      liftToTotal ≫ L.liftStructureMap ≫ w₂FrobeniusSpec p k
  specialFiberMap :
    LocalFrobeniusLift.specialFiber L liftToTotal ⟶
      LocalFrobeniusLift.specialFiber L liftToTotal
  specialFiberMap_fst :
    specialFiberMap ≫ pullback.fst _ _ = pullback.fst _ _ ≫ liftFrob
  specialFiberMap_snd :
    specialFiberMap ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ fieldFrobeniusSpec p k
  reduction_eq :
    specialFiberIso.inv ≫ specialFiberMap ≫ specialFiberIso.hom = frobenius

attribute [instance] LocalFrobeniusLift.liftToTotal_open
attribute [instance] LocalFrobeniusLift.lift_affine

namespace LocalFrobeniusLift

variable {L : W₂Lift (p := p) (k := k) X}
variable {U : AlgebraicGeometry.Scheme.{u}} {j : U ⟶ X} {F : X ⟶ X}

/-- A lifted local chart is itself a `W₂(k)`-lifting of its special fibre.
This is the bridge which lets the separately defined global LSZ functor be
used verbatim on every affine member of an atlas. -/
noncomputable def toW₂Lift (Phi : LocalFrobeniusLift L j F)
    [AlgebraicGeometry.IsOpenImmersion j] :
    W₂Lift (p := p) (k := k) U where
  structureMap := j ≫ L.structureMap
  smooth := by
    letI : AlgebraicGeometry.Smooth L.structureMap := L.smooth
    infer_instance
  lift := Phi.lift
  liftStructureMap := Phi.liftToTotal ≫ L.liftStructureMap
  liftSmooth := by
    letI : AlgebraicGeometry.Smooth L.liftStructureMap := L.liftSmooth
    infer_instance
  specialFiberIso := Phi.specialFiberIso
  specialFiberIso_over := by
    calc
      Phi.specialFiberIso.hom ≫ j ≫ L.structureMap =
          (toTotalSpecialFiber L Phi.liftToTotal ≫
            L.specialFiberIso.hom) ≫ L.structureMap := by
              rw [← Category.assoc, Phi.specialFiberIso_toX]
      _ = toTotalSpecialFiber L Phi.liftToTotal ≫
          (L.specialFiberIso.hom ≫ L.structureMap) :=
            Category.assoc _ _ _
      _ = toTotalSpecialFiber L Phi.liftToTotal ≫ pullback.snd _ _ := by
            rw [L.specialFiberIso_over]
      _ = pullback.snd _ _ := toTotalSpecialFiber_snd L Phi.liftToTotal

/-- The local Frobenius lifting, viewed as a global Frobenius lifting of
the local `W₂(k)`-scheme supplied by `toW₂Lift`. -/
noncomputable def toGlobalFrobeniusLift (Phi : LocalFrobeniusLift L j F)
    [AlgebraicGeometry.IsOpenImmersion j] :
    GlobalFrobeniusLift U Phi.toW₂Lift where
  frobenius := Phi.frobenius
  liftFrob := Phi.liftFrob
  liftFrob_over := by
    simpa only [toW₂Lift, Category.assoc] using Phi.liftFrob_over
  specialFiberMap := Phi.specialFiberMap
  specialFiberMap_fst := Phi.specialFiberMap_fst
  specialFiberMap_snd := Phi.specialFiberMap_snd
  reduction_eq := Phi.reduction_eq

end LocalFrobeniusLift

/-- An affine cover of `X` together with a lifted affine chart and a local
Frobenius lifting on every member.  All local reductions are restrictions
of the same endomorphism `frobenius : X ⟶ X`.

The intended LSZ hypotheses additionally assume that `k` is perfect and
that `p` is odd; those hypotheses are placed on the construction theorem,
not duplicated in this purely geometric record.
-/
structure AffineFrobeniusAtlas
    (L : W₂Lift (p := p) (k := k) X) where
  perfect : PerfectField k
  oddPrime : p ≠ 2
  frobenius : X ⟶ X
  cover : X.AffineOpenCover
  localLift (i : cover.I₀) :
    LocalFrobeniusLift L (cover.f i) frobenius

namespace AffineFrobeniusAtlas

variable {L : W₂Lift (p := p) (k := k) X}

/-- The `i`-th affine open of an LSZ atlas, viewed as a scheme. -/
noncomputable abbrev chart (A : AffineFrobeniusAtlas L) (i : A.cover.I₀) :
    AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (A.cover.X i)

@[reassoc]
lemma local_frobenius_commutes (A : AffineFrobeniusAtlas L)
    (i : A.cover.I₀) :
    (A.localLift i).frobenius ≫ A.cover.f i =
      A.cover.f i ≫ A.frobenius :=
  (A.localLift i).frobenius_toX

end AffineFrobeniusAtlas

end LSZ
