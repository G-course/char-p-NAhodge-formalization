import LSZ.CanonicalConnection
import LSZ.FrobeniusPullback
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The canonical connection on mathlib's Frobenius extension of scalars

For a `k`-algebra `A` in characteristic `p`, mathlib represents pullback of
an affine module along Frobenius by

`ModuleCat.extendScalars (algebraFrobenius k A p)`.

This file puts the canonical flat connection directly on that standard
object.  It first identifies the standard tensor product with the tagged
tensor product from `LSZ.CanonicalConnection`, and then transports the
already proved connection.  In particular, the construction uses no custom
presheaf model.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry TensorProduct ModuleCat.Algebra ChangeOfRings

namespace LSZ

universe u₁ u₂ u₃ u₄

noncomputable section

section Affine

variable (k : Type u₁) (A : Type u₂) (M : Type u₃) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [AddCommGroup M] [Module A M]
variable [CharP k p] [Fact p.Prime]

namespace StandardFrobeniusPullback

/-- Mathlib's standard extension-of-scalars model for
`A ⊗_{A,F_A} M`. -/
abbrev obj : Type (max u₂ u₃) :=
  (ModuleCat.extendScalars (algebraFrobenius k A p)).obj (ModuleCat.of A M)

/-- Package the left tensor factor with the restriction-of-scalars type
expected by mathlib's tensor-product implementation. -/
def leftPack : A →+
    (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
      (ModuleCat.of A A) where
  toFun a := a
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Package the coefficient in the standard `ModuleCat` object. -/
def coefficientPack : M →+ ModuleCat.of A M where
  toFun m := m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- An elementary tensor in mathlib's standard Frobenius pullback. -/
def tmul (a : A) (m : M) : obj k A M p :=
  leftPack k A p a ⊗ₜ[A] coefficientPack A M m

@[simp]
lemma tmul_zero (a : A) : tmul k A M p a 0 = 0 := by
  unfold tmul
  rw [map_zero, TensorProduct.tmul_zero]
  rfl

@[simp]
lemma zero_tmul (m : M) : tmul k A M p 0 m = 0 := by
  unfold tmul
  rw [map_zero, TensorProduct.zero_tmul]
  rfl

lemma add_tmul (a b : A) (m : M) :
    tmul k A M p (a + b) m =
      tmul k A M p a m + tmul k A M p b m := by
  unfold tmul
  rw [map_add, TensorProduct.add_tmul]
  rfl

lemma tmul_add (a : A) (m n : M) :
    tmul k A M p a (m + n) =
      tmul k A M p a m + tmul k A M p a n := by
  unfold tmul
  rw [map_add, TensorProduct.tmul_add]
  rfl

/-- The additive map from mathlib's standard tensor to the tagged tensor. -/
def toCustomAdd : obj k A M p →+
    AffineFrobeniusPullback k A M p := by
  let f := algebraFrobenius k A p
  let Sres := (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)
  let N := ModuleCat.of A M
  let Q := AffineFrobeniusPullback k A M p
  let b : Sres →+ N →+ Q :=
    { toFun := fun a ↦
        { toFun := fun m ↦ AffineFrobeniusPullback.tmul k A M p
            (show A from a) (show M from m)
          map_zero' := by
            unfold AffineFrobeniusPullback.tmul
            change (show A from a) ⊗ₜ[FrobeniusSource k A p]
              FrobeniusCoefficient.mk (0 : M) = 0
            have hz : FrobeniusCoefficient.mk (0 : M) = 0 := by
              apply (FrobeniusCoefficient.equiv M).injective
              rfl
            rw [hz, TensorProduct.tmul_zero]
          map_add' := by
            intro m n
            unfold AffineFrobeniusPullback.tmul
            change (show A from a) ⊗ₜ[FrobeniusSource k A p]
                FrobeniusCoefficient.mk ((show M from m) + (show M from n)) = _
            have hadd : FrobeniusCoefficient.mk
                ((show M from m) + (show M from n)) =
                FrobeniusCoefficient.mk (show M from m) +
                  FrobeniusCoefficient.mk (show M from n) := by
              apply (FrobeniusCoefficient.equiv M).injective
              rfl
            rw [hadd, TensorProduct.tmul_add] }
      map_zero' := by
        ext m
        unfold AffineFrobeniusPullback.tmul
        change (0 : A) ⊗ₜ[FrobeniusSource k A p]
            FrobeniusCoefficient.mk (show M from m) = 0
        rw [TensorProduct.zero_tmul]
      map_add' := by
        intro a b
        ext m
        unfold AffineFrobeniusPullback.tmul
        change ((show A from a) + (show A from b)) ⊗ₜ[FrobeniusSource k A p]
            FrobeniusCoefficient.mk (show M from m) = _
        rw [TensorProduct.add_tmul]
        rfl }
  refine TensorProduct.liftAddHom b ?_
  intro r a m
  dsimp [b]
  unfold AffineFrobeniusPullback.tmul
  change (r ^ p • (show A from a)) ⊗ₜ[FrobeniusSource k A p]
      FrobeniusCoefficient.mk (show M from m) =
    (show A from a) ⊗ₜ[FrobeniusSource k A p]
      FrobeniusCoefficient.mk (r • (show M from m))
  have ha : r ^ p • (show A from a) =
      (FrobeniusSource.mk r : FrobeniusSource k A p) •
        (show A from a) := by
    change r ^ p * (show A from a) =
      algebraFrobenius k A p r * (show A from a)
    rw [algebraFrobenius_apply]
  have hm : FrobeniusCoefficient.mk (r • (show M from m)) =
      (FrobeniusSource.mk r : FrobeniusSource k A p) •
        FrobeniusCoefficient.mk (show M from m) := by
    apply (FrobeniusCoefficient.equiv M).injective
    rfl
  rw [ha, hm, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

@[simp]
lemma toCustomAdd_tmul (a : A) (m : M) :
    toCustomAdd k A M p (tmul k A M p a m) =
      AffineFrobeniusPullback.tmul k A M p a m := rfl

/-- The additive inverse from the tagged tensor to mathlib's standard
tensor. -/
def fromCustomAdd : AffineFrobeniusPullback k A M p →+
    obj k A M p := by
  let f := algebraFrobenius k A p
  let Sres := (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)
  let N := ModuleCat.of A M
  let P := obj k A M p
  let b : (ModuleCat.of (FrobeniusSource k A p) A) →+
      (ModuleCat.of (FrobeniusSource k A p)
        (FrobeniusCoefficient M)) →+ P :=
    { toFun := fun a ↦
        { toFun := fun m ↦ tmul k A M p a m.down
          map_zero' := by
            have hz : (0 : FrobeniusCoefficient M).down = 0 := rfl
            rw [hz, tmul_zero]
          map_add' := by
            intro m n
            have hadd : (m + n).down = m.down + n.down := rfl
            rw [hadd, tmul_add] }
      map_zero' := by
        ext m
        change tmul k A M p
          (show A from (0 : ModuleCat.of (FrobeniusSource k A p) A)) m.down = 0
        have hz : (show A from (0 : ModuleCat.of
            (FrobeniusSource k A p) A)) = 0 := rfl
        rw [hz, zero_tmul]
      map_add' := by
        intro a b
        ext m
        change tmul k A M p (show A from a + b) m.down =
          tmul k A M p (show A from a) m.down +
            tmul k A M p (show A from b) m.down
        have hadd : (show A from a + b) =
            (show A from a) + (show A from b) := rfl
        rw [hadd, add_tmul] }
  refine TensorProduct.liftAddHom b ?_
  intro r a m
  dsimp [b]
  unfold tmul
  let rA : A := r.down
  change (rA • (show Sres from a)) ⊗ₜ[A]
      (show N from m.down) =
    (show Sres from a) ⊗ₜ[A]
      (rA • (show N from m.down))
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

@[simp]
lemma fromCustomAdd_tmul (a : A) (m : M) :
    fromCustomAdd k A M p (AffineFrobeniusPullback.tmul k A M p a m) =
      tmul k A M p a m := rfl

lemma from_to (x : obj k A M p) :
    fromCustomAdd k A M p (toCustomAdd k A M p x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul a m => rfl
  | add x y hx hy =>
      let x' : obj k A M p := x
      let y' : obj k A M p := y
      change fromCustomAdd k A M p
          (toCustomAdd k A M p (x' + y')) = x' + y'
      rw [map_add, map_add]
      change fromCustomAdd k A M p (toCustomAdd k A M p x') +
          fromCustomAdd k A M p (toCustomAdd k A M p y') = x' + y'
      simpa [x', y'] using congrArg₂ (fun a b ↦ a + b) hx hy

lemma to_from (x : AffineFrobeniusPullback k A M p) :
    toCustomAdd k A M p (fromCustomAdd k A M p x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul a m => rfl
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

lemma toCustomAdd_smul (r : A) (x : obj k A M p) :
    toCustomAdd k A M p (r • x) =
      r • toCustomAdd k A M p x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change toCustomAdd k A M p (0 : obj k A M p) = 0
      rw [map_zero]
  | tmul a m =>
      change AffineFrobeniusPullback.tmul k A M p
          (r * (show A from a)) (show M from m) =
        r • AffineFrobeniusPullback.tmul k A M p
          (show A from a) (show M from m)
      unfold AffineFrobeniusPullback.tmul
      rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy =>
      let x' : obj k A M p := x
      let y' : obj k A M p := y
      change toCustomAdd k A M p (r • (x' + y')) =
        r • toCustomAdd k A M p (x' + y')
      rw [smul_add, map_add, map_add, smul_add]
      change toCustomAdd k A M p (r • x') +
          toCustomAdd k A M p (r • y') =
        r • toCustomAdd k A M p x' +
          r • toCustomAdd k A M p y'
      simpa [x', y'] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- The standard mathlib extension-of-scalars tensor is linearly equivalent
to the tagged tensor used in `AffineFrobeniusPullback`. -/
def linearEquiv : obj k A M p ≃ₗ[A]
    AffineFrobeniusPullback k A M p where
  toFun := toCustomAdd k A M p
  invFun := fromCustomAdd k A M p
  left_inv := from_to k A M p
  right_inv := to_from k A M p
  map_add' := map_add (toCustomAdd k A M p)
  map_smul' := toCustomAdd_smul k A M p

@[simp]
lemma linearEquiv_tmul (a : A) (m : M) :
    linearEquiv k A M p (tmul k A M p a m) =
      AffineFrobeniusPullback.tmul k A M p a m := rfl

/-- The same comparison, viewed as a `k`-linear equivalence. -/
def kLinearEquiv : obj k A M p ≃ₗ[k]
    AffineFrobeniusPullback k A M p :=
  (linearEquiv k A M p).restrictScalars k

@[simp]
lemma kLinearEquiv_apply (x : obj k A M p) :
    kLinearEquiv k A M p x = linearEquiv k A M p x := rfl

@[simp]
lemma kLinearEquiv_symm_apply (x : AffineFrobeniusPullback k A M p) :
    (kLinearEquiv k A M p).symm x =
      (linearEquiv k A M p).symm x := rfl

/-- The canonical covariant derivative on mathlib's standard
extension-of-scalars object, transported from the tagged construction. -/
def canonicalNablaEnd (D : Derivation k A A) :
    Module.End k (obj k A M p) where
  toFun x := (linearEquiv k A M p).symm
    (AffineFrobeniusPullback.canonicalNabla k A M p D
      (linearEquiv k A M p x))
  map_add' := by
    intro x y
    simp only [map_add]
  map_smul' := by
    intro c x
    exact (((kLinearEquiv k A M p).symm.toLinearMap.comp
      ((AffineFrobeniusPullback.canonicalNabla k A M p D).comp
        (kLinearEquiv k A M p).toLinearMap))).map_smul c x

@[simp]
lemma canonicalNablaEnd_tmul (D : Derivation k A A) (a : A) (m : M) :
    canonicalNablaEnd k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := by
  rfl

@[simp]
lemma linearEquiv_canonicalNablaEnd_apply (D : Derivation k A A)
    (x : obj k A M p) :
    linearEquiv k A M p (canonicalNablaEnd k A M p D x) =
      AffineFrobeniusPullback.canonicalNabla k A M p D
        (linearEquiv k A M p x) := by
  change linearEquiv k A M p
      ((linearEquiv k A M p).symm
        (AffineFrobeniusPullback.canonicalNabla k A M p D
          (linearEquiv k A M p x))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The canonical connection is `A`-linear in the tangent direction. -/
def canonicalNabla : Tangent k A →ₗ[A]
    Module.End k (obj k A M p) where
  toFun := canonicalNablaEnd k A M p
  map_add' := by
    intro D E
    ext x
    apply (linearEquiv k A M p).injective
    change linearEquiv k A M p
        (canonicalNablaEnd k A M p (D + E) x) =
      linearEquiv k A M p
        (canonicalNablaEnd k A M p D x +
          canonicalNablaEnd k A M p E x)
    rw [LinearEquiv.map_add]
    rw [linearEquiv_canonicalNablaEnd_apply,
      linearEquiv_canonicalNablaEnd_apply,
      linearEquiv_canonicalNablaEnd_apply]
    have h := congrArg
      (fun T : Module.End k (AffineFrobeniusPullback k A M p) ↦
        T (linearEquiv k A M p x))
      (map_add (AffineFrobeniusPullback.canonicalNabla k A M p) D E)
    simpa only [LinearMap.add_apply] using h
  map_smul' := by
    intro r D
    ext x
    apply (linearEquiv k A M p).injective
    change linearEquiv k A M p
        (canonicalNablaEnd k A M p (r • D) x) =
      linearEquiv k A M p
        (r • canonicalNablaEnd k A M p D x)
    rw [LinearEquiv.map_smul]
    rw [linearEquiv_canonicalNablaEnd_apply,
      linearEquiv_canonicalNablaEnd_apply]
    have h := congrArg
      (fun T : Module.End k (AffineFrobeniusPullback k A M p) ↦
        T (linearEquiv k A M p x))
      (map_smul (AffineFrobeniusPullback.canonicalNabla k A M p) r D)
    simpa only [LinearMap.smul_apply, RingHom.id_apply] using h

@[simp]
lemma canonicalNabla_tmul (D : Tangent k A) (a : A) (m : M) :
    canonicalNabla k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := by
  rfl

@[simp]
lemma linearEquiv_canonicalNabla_apply (D : Tangent k A)
    (x : obj k A M p) :
    linearEquiv k A M p (canonicalNabla k A M p D x) =
      AffineFrobeniusPullback.canonicalNabla k A M p D
        (linearEquiv k A M p x) :=
  linearEquiv_canonicalNablaEnd_apply k A M p D x

/-- The canonical flat connection on the object produced by
`ModuleCat.extendScalars (algebraFrobenius k A p)`. -/
def canonicalConnection :
    IntegrableConnection k A (obj k A M p) where
  nabla := canonicalNabla k A M p
  leibniz := by
    intro D a x
    apply (linearEquiv k A M p).injective
    change linearEquiv k A M p
        (canonicalNabla k A M p D (a • x)) =
      linearEquiv k A M p
        (a • canonicalNabla k A M p D x + D a • x)
    rw [map_add, LinearEquiv.map_smul, LinearEquiv.map_smul]
    rw [linearEquiv_canonicalNabla_apply,
      linearEquiv_canonicalNabla_apply]
    rw [LinearEquiv.map_smul]
    exact (AffineFrobeniusPullback.canonicalConnection k A M p).leibniz
      D a (linearEquiv k A M p x)
  flat := by
    intro D E x
    apply (linearEquiv k A M p).injective
    change linearEquiv k A M p
        (canonicalNabla k A M p ⁅D, E⁆ x) =
      linearEquiv k A M p
        (canonicalNabla k A M p D (canonicalNabla k A M p E x) -
          canonicalNabla k A M p E (canonicalNabla k A M p D x))
    rw [map_sub]
    rw [linearEquiv_canonicalNabla_apply,
      linearEquiv_canonicalNabla_apply,
      linearEquiv_canonicalNabla_apply,
      linearEquiv_canonicalNabla_apply,
      linearEquiv_canonicalNabla_apply]
    exact (AffineFrobeniusPullback.canonicalConnection k A M p).flat
      D E (linearEquiv k A M p x)

end StandardFrobeniusPullback

namespace IntegrableConnection

variable (k : Type u₁) (A : Type u₂)
variable (M : Type u₃) (N : Type u₄)
variable [CommRing k] [CommRing A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable {p : ℕ} [CharP k p] [CharP A p] [Fact p.Prime]

/-- Conjugate one covariant derivative by an `A`-linear equivalence. -/
def transportNablaEnd (e : N ≃ₗ[A] M)
    (C : IntegrableConnection k A M) (D : Tangent k A) :
    Module.End k N :=
  ((e.restrictScalars k).symm.toLinearMap.comp
    ((C.nabla D).comp (e.restrictScalars k).toLinearMap))

@[simp]
lemma apply_transportNablaEnd (e : N ≃ₗ[A] M)
    (C : IntegrableConnection k A M) (D : Tangent k A) (x : N) :
    e (transportNablaEnd k A M N e C D x) = C.nabla D (e x) := by
  change e (e.symm (C.nabla D (e x))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The transported connection map; it remains `A`-linear in the tangent
direction. -/
def transportNabla (e : N ≃ₗ[A] M)
    (C : IntegrableConnection k A M) :
    Tangent k A →ₗ[A] Module.End k N where
  toFun := transportNablaEnd k A M N e C
  map_add' := by
    intro D E
    ext x
    apply e.injective
    change e (transportNablaEnd k A M N e C (D + E) x) =
      e (transportNablaEnd k A M N e C D x +
        transportNablaEnd k A M N e C E x)
    rw [LinearEquiv.map_add]
    rw [apply_transportNablaEnd, apply_transportNablaEnd,
      apply_transportNablaEnd]
    have h := congrArg (fun T : Module.End k M ↦ T (e x))
      (map_add C.nabla D E)
    simpa only [LinearMap.add_apply] using h
  map_smul' := by
    intro r D
    ext x
    apply e.injective
    change e (transportNablaEnd k A M N e C (r • D) x) =
      e (r • transportNablaEnd k A M N e C D x)
    rw [LinearEquiv.map_smul]
    rw [apply_transportNablaEnd, apply_transportNablaEnd]
    have h := congrArg (fun T : Module.End k M ↦ T (e x))
      (map_smul C.nabla r D)
    simpa only [LinearMap.smul_apply, RingHom.id_apply] using h

@[simp]
lemma apply_transportNabla (e : N ≃ₗ[A] M)
    (C : IntegrableConnection k A M) (D : Tangent k A) (x : N) :
    e (transportNabla k A M N e C D x) = C.nabla D (e x) :=
  apply_transportNablaEnd k A M N e C D x

/-- Transport an integrable connection along an `A`-linear equivalence.
Leibniz and flatness are proved after conjugation, rather than inserted as
additional data. -/
def transport (e : N ≃ₗ[A] M)
    (C : IntegrableConnection k A M) : IntegrableConnection k A N where
  nabla := transportNabla k A M N e C
  leibniz := by
    intro D a x
    apply e.injective
    change e (transportNabla k A M N e C D (a • x)) =
      e (a • transportNabla k A M N e C D x + D a • x)
    rw [map_add, LinearEquiv.map_smul, LinearEquiv.map_smul]
    rw [apply_transportNabla, apply_transportNabla]
    rw [LinearEquiv.map_smul]
    exact C.leibniz D a (e x)
  flat := by
    intro D E x
    apply e.injective
    change e (transportNabla k A M N e C ⁅D, E⁆ x) =
      e (transportNabla k A M N e C D
          (transportNabla k A M N e C E x) -
        transportNabla k A M N e C E
          (transportNabla k A M N e C D x))
    rw [map_sub]
    rw [apply_transportNabla, apply_transportNabla,
      apply_transportNabla, apply_transportNabla, apply_transportNabla]
    exact C.flat D E (e x)

end IntegrableConnection

end Affine

section Scheme

variable {p : ℕ} {k : Type u₁}
variable [Field k] [CharP k p] [Fact p.Prime]

namespace SmoothScheme

/-- On a smooth `k`-scheme, the intrinsically defined absolute Frobenius map
on the coordinate ring of an open is the algebraic `p`-power Frobenius.

This lemma is only a comparison after a ground field has been chosen.  The
scheme morphism `Scheme.absoluteFrobenius` itself was defined for every
intrinsic characteristic-`p` scheme and does not use smoothness. -/
lemma absoluteFrobenius_app_eq_algebraFrobenius (X : SmoothScheme k)
    (U : X.scheme.Opens) :
    ((AlgebraicGeometry.Scheme.absoluteFrobenius
      (p := p) X.scheme).app U).hom =
      algebraFrobenius k Γ(X.scheme, U) p := by
  ext a
  exact (AlgebraicGeometry.Scheme.absoluteFrobenius_app_apply
    (p := p) X.scheme U a).trans
      (algebraFrobenius_apply k Γ(X.scheme, U) p a).symm

end SmoothScheme

namespace FrobeniusPullback

/-- The canonical flat connection on the affine Frobenius twist which occurs
as the local module of sections of `Scheme.Modules.pullback F_X`.

After unfolding `twist`, the preceding comparison identifies its ring map
with `algebraFrobenius`; the connection is therefore the verified standard
affine construction. -/
def twistCanonicalConnection (X : SmoothScheme k) (U : X.scheme.Opens)
    (M : ModuleCat Γ(X.scheme, U)) :
    IntegrableConnection k Γ(X.scheme, U)
      (twist (p := p) X.scheme U M) := by
  unfold twist
  rw [SmoothScheme.absoluteFrobenius_app_eq_algebraFrobenius]
  exact StandardFrobeniusPullback.canonicalConnection
    k Γ(X.scheme, U) M p

/-- The canonical flat connection on the actual affine-local sections of
mathlib's Frobenius pullback.  The connection on the Frobenius twist is
transported back through `restrictedTopIso`; consequently the carrier here
is the left side of the sheaf-theoretic affine comparison, not an auxiliary
tensor model. -/
def restrictedCanonicalConnection (X : SmoothScheme k)
    (U : X.scheme.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (F : X.scheme.Modules) [F.IsQuasicoherent] :
    IntegrableConnection k Γ(X.scheme, U)
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X.scheme, U))).obj
        (restrictedCarrierChart (p := p) X.scheme U hU F)) :=
  IntegrableConnection.transport k Γ(X.scheme, U) _ _
    (restrictedTopIso (p := p) X.scheme U hU F).toLinearEquiv
    (twistCanonicalConnection X U
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X.scheme, U))).obj
        (chartModule X.scheme U hU F)))

set_option maxRecDepth 2000 in
/-- The affine comparison `restrictedTopIso` is horizontal for the canonical
connections.  This records explicitly that the connection on the actual
Frobenius pullback is the transported tensor-product connection. -/
@[simp]
lemma restrictedTopIso_nabla (X : SmoothScheme k)
    (U : X.scheme.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (F : X.scheme.Modules) [F.IsQuasicoherent]
    (D : Tangent k Γ(X.scheme, U))
    (x : (AlgebraicGeometry.moduleSpecΓFunctor
      (R := Γ(X.scheme, U))).obj
        (restrictedCarrierChart (p := p) X.scheme U hU F)) :
    (restrictedTopIso (p := p) X.scheme U hU F).hom
        ((restrictedCanonicalConnection X U hU F).nabla D x) =
      (twistCanonicalConnection X U
        ((AlgebraicGeometry.moduleSpecΓFunctor
          (R := Γ(X.scheme, U))).obj
            (chartModule X.scheme U hU F))).nabla D
        ((restrictedTopIso (p := p) X.scheme U hU F).hom x) :=
  IntegrableConnection.apply_transportNabla k Γ(X.scheme, U) _ _
    (restrictedTopIso (p := p) X.scheme U hU F).toLinearEquiv
    (twistCanonicalConnection X U
      ((AlgebraicGeometry.moduleSpecΓFunctor
        (R := Γ(X.scheme, U))).obj
          (chartModule X.scheme U hU F))) D x

end FrobeniusPullback

end Scheme

end

end LSZ
