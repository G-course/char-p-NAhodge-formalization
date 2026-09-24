import LSZ.AbsoluteFrobenius
import LSZ.Objects
import LSZ.FrobeniusPullback
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The canonical connection on Frobenius extension of scalars

For a `k`-algebra `A` in characteristic `p`, mathlib represents affine
Frobenius pullback by

`ModuleCat.extendScalars (algebraFrobenius k A p)`.

This file constructs the canonical flat connection directly on that
standard object:

`∇ᶜᵃⁿ_D (a ⊗ m) = D(a) ⊗ m`.

No second tensor-product model is introduced. The two packaging maps below
only expose pure tensors while keeping mathlib's opaque
restriction-of-scalars carrier definitionally stable.
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

set_option backward.isDefEq.respectTransparency false

/-- Mathlib's standard extension-of-scalars object `A ⊗_{A,F_A} M`. -/
abbrev obj : ModuleCat A :=
  (ModuleCat.extendScalars (algebraFrobenius k A p)).obj (ModuleCat.of A M)

/-- Package the left tensor factor in the restriction-of-scalars carrier
used internally by `ModuleCat.extendScalars`. -/
def leftPack : A →+
    (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
      (ModuleCat.of A A) where
  toFun a := a
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Package a coefficient in the input `ModuleCat` object. -/
def coefficientPack : M →+ ModuleCat.of A M where
  toFun m := m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A pure tensor in mathlib's Frobenius extension of scalars. -/
def tmul (a : A) (m : M) : obj k A M p :=
  leftPack k A p a ⊗ₜ[A] coefficientPack A M m

@[simp]
lemma tmul_zero (a : A) : tmul k A M p a 0 = 0 := by
  unfold tmul
  rw [map_zero, TensorProduct.tmul_zero]

@[simp]
lemma zero_tmul (m : M) : tmul k A M p 0 m = 0 := by
  unfold tmul
  rw [map_zero, TensorProduct.zero_tmul]

lemma add_tmul (a b : A) (m : M) :
    tmul k A M p (a + b) m =
      tmul k A M p a m + tmul k A M p b m := by
  unfold tmul
  rw [map_add, TensorProduct.add_tmul]

lemma tmul_add (a : A) (m n : M) :
    tmul k A M p a (m + n) =
      tmul k A M p a m + tmul k A M p a n := by
  unfold tmul
  rw [map_add, TensorProduct.tmul_add]

lemma sub_tmul (a b : A) (m : M) :
    tmul k A M p (a - b) m =
      tmul k A M p a m - tmul k A M p b m := by
  unfold tmul
  rw [map_sub, TensorProduct.sub_tmul]

@[simp]
lemma smul_tmul (r a : A) (m : M) :
    r • tmul k A M p a m = tmul k A M p (r * a) m := by
  rfl

/-- The balancing relation, stated without exposing the internal
restriction-of-scalars carrier. -/
lemma tmul_smul (a r : A) (m : M) :
    tmul k A M p a (r • m) =
      algebraFrobenius k A p r • tmul k A M p a m := by
  unfold tmul
  have hm : coefficientPack A M (r • m) =
      r • coefficientPack A M m := rfl
  rw [hm, TensorProduct.tmul_smul]
  rfl

/-- A relative derivation kills the image of absolute Frobenius. -/
lemma derivation_frobenius_eq_zero (D : Derivation k A A) (a : A) :
    D (algebraFrobenius k A p a) = 0 := by
  rw [algebraFrobenius_apply, D.leibniz_pow]
  have hpA : (p : A) = 0 := by
    calc
      (p : A) = algebraMap k A (p : k) := by rw [map_natCast]
      _ = algebraMap k A 0 := by rw [CharP.cast_eq_zero]
      _ = 0 := map_zero _
  simpa only [← Nat.cast_smul_eq_nsmul A, hpA, zero_smul]

/-- The additive pairing used to define the canonical derivative on the
tensor product. -/
def canonicalPairing (D : Derivation k A A) :
    (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
        (ModuleCat.of A A) →+
      ModuleCat.of A M →+ obj k A M p :=
  { toFun := fun a ↦
      { toFun := fun m ↦
          tmul k A M p (D (show A from a)) (show M from m)
        map_zero' := tmul_zero k A M p _
        map_add' := tmul_add k A M p _ }
    map_zero' := by
      ext m
      change tmul k A M p (D 0) (show M from m) = 0
      rw [map_zero, zero_tmul]
    map_add' := by
      intro a b
      ext m
      change tmul k A M p (D ((show A from a) + (show A from b)))
          (show M from m) = _
      rw [map_add, add_tmul]
      rfl }

/-- The preceding pairing is balanced over the Frobenius source action. -/
lemma canonicalPairing_balanced (D : Derivation k A A)
    (r : A)
    (a : (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
      (ModuleCat.of A A)) (m : ModuleCat.of A M) :
    canonicalPairing k A M p D (r • a) m =
      canonicalPairing k A M p D a (r • m) := by
  change tmul k A M p
      (D (algebraFrobenius k A p r * (show A from a)))
        (show M from m) =
    tmul k A M p (D (show A from a)) (r • (show M from m))
  rw [D.leibniz, derivation_frobenius_eq_zero k A p D r,
    smul_zero, add_zero, tmul_smul]
  exact (smul_tmul k A M p (algebraFrobenius k A p r)
    (D (show A from a)) (show M from m)).symm

/-- The additive canonical derivative in one tangent direction. -/
def canonicalNablaAdd (D : Derivation k A A) :
    obj k A M p →+ obj k A M p :=
  TensorProduct.liftAddHom (canonicalPairing k A M p D)
    (canonicalPairing_balanced k A M p D)

@[simp]
lemma canonicalNablaAdd_tmul (D : Derivation k A A) (a : A) (m : M) :
    canonicalNablaAdd k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := by
  rfl

/-- Leibniz rule for the additive canonical derivative. -/
lemma canonicalNablaAdd_leibniz (D : Tangent k A) (a : A)
    (x : obj k A M p) :
    canonicalNablaAdd k A M p D (a • x) =
      a • canonicalNablaAdd k A M p D x + D a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero, add_zero]
  | tmul b m =>
      change tmul k A M p (D (a * (show A from b))) (show M from m) =
        a • tmul k A M p (D (show A from b)) (show M from m) +
          D a • tmul k A M p (show A from b) (show M from m)
      rw [D.leibniz, add_tmul, smul_tmul, smul_tmul]
      congr 2
      exact mul_comm _ _
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy, smul_add, smul_add]
      abel

/-- The canonical derivative in one direction as a `k`-linear
endomorphism. -/
def canonicalNablaEnd (D : Derivation k A A) :
    Module.End k (obj k A M p) where
  toFun := canonicalNablaAdd k A M p D
  map_add' := map_add _
  map_smul' := by
    intro c x
    calc
      canonicalNablaAdd k A M p D (c • x) =
          canonicalNablaAdd k A M p D (algebraMap k A c • x) :=
        congrArg (canonicalNablaAdd k A M p D)
          (IsScalarTower.algebraMap_smul A c x).symm
      _ = algebraMap k A c • canonicalNablaAdd k A M p D x +
          D (algebraMap k A c) • x :=
        canonicalNablaAdd_leibniz k A M p D (algebraMap k A c) x
      _ = algebraMap k A c • canonicalNablaAdd k A M p D x := by
        rw [D.map_algebraMap, zero_smul, add_zero]
      _ = c • canonicalNablaAdd k A M p D x :=
        IsScalarTower.algebraMap_smul A c _

@[simp]
lemma canonicalNablaEnd_tmul (D : Derivation k A A) (a : A) (m : M) :
    canonicalNablaEnd k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := rfl

/-- The canonical derivative, linear in the tangent direction. -/
def canonicalNabla :
    Tangent k A →ₗ[A] Module.End k (obj k A M p) where
  toFun := canonicalNablaEnd k A M p
  map_add' := by
    intro D E
    ext x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
        change tmul k A M p ((D + E) (show A from a))
            (show M from m) = _
        rw [Derivation.add_apply, add_tmul]
        rfl
    | add x y hx hy =>
        let x' : obj k A M p := x
        let y' : obj k A M p := y
        change canonicalNablaEnd k A M p (D + E) x' =
          (canonicalNablaEnd k A M p D +
            canonicalNablaEnd k A M p E) x' at hx
        change canonicalNablaEnd k A M p (D + E) y' =
          (canonicalNablaEnd k A M p D +
            canonicalNablaEnd k A M p E) y' at hy
        change canonicalNablaEnd k A M p (D + E) (x' + y') =
          (canonicalNablaEnd k A M p D +
            canonicalNablaEnd k A M p E) (x' + y')
        rw [map_add, LinearMap.add_apply, map_add, map_add]
        rw [hx, hy, LinearMap.add_apply, LinearMap.add_apply]
        abel
  map_smul' := by
    intro r D
    ext x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
        change tmul k A M p (r * D (show A from a))
            (show M from m) =
          r • tmul k A M p (D (show A from a)) (show M from m)
        rw [smul_tmul]
    | add x y hx hy =>
        let x' : obj k A M p := x
        let y' : obj k A M p := y
        change canonicalNablaEnd k A M p (r • D) x' =
          (r • canonicalNablaEnd k A M p D) x' at hx
        change canonicalNablaEnd k A M p (r • D) y' =
          (r • canonicalNablaEnd k A M p D) y' at hy
        change canonicalNablaEnd k A M p (r • D) (x' + y') =
          (r • canonicalNablaEnd k A M p D) (x' + y')
        rw [map_add, LinearMap.smul_apply, map_add, smul_add]
        exact congrArg₂ (fun u v ↦ u + v) hx hy

@[simp]
lemma canonicalNabla_tmul (D : Tangent k A) (a : A) (m : M) :
    canonicalNabla k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := rfl

/-- Vanishing curvature of the canonical derivative. -/
lemma canonicalNabla_flat (D E : Tangent k A) (x : obj k A M p) :
    canonicalNabla k A M p ⁅D, E⁆ x =
      canonicalNabla k A M p D (canonicalNabla k A M p E x) -
        canonicalNabla k A M p E (canonicalNabla k A M p D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | tmul a m =>
      change tmul k A M p (⁅D, E⁆ (show A from a)) (show M from m) =
        tmul k A M p (D (E (show A from a))) (show M from m) -
          tmul k A M p (E (D (show A from a))) (show M from m)
      rw [Derivation.commutator_apply, sub_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, map_add, hx, hy]
      abel

/-- Mathlib's Frobenius extension of scalars with its canonical flat
connection. -/
def canonicalConnection :
    IntegrableConnection k A (obj k A M p) where
  nabla := canonicalNabla k A M p
  leibniz := canonicalNablaAdd_leibniz k A M p
  flat := canonicalNabla_flat k A M p

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

/-- Transport an integrable connection along an `A`-linear equivalence. -/
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

/-- On a smooth `k`-scheme, absolute Frobenius acts on functions by the
algebraic `p`-power Frobenius. -/
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

/-- The canonical flat connection on the affine Frobenius twist occurring
as the local module of sections of scheme-theoretic Frobenius pullback. -/
def twistCanonicalConnection (X : SmoothScheme k) (U : X.scheme.Opens)
    (M : ModuleCat Γ(X.scheme, U)) :
    IntegrableConnection k Γ(X.scheme, U)
      (twist (p := p) X.scheme U M) := by
  unfold twist
  rw [SmoothScheme.absoluteFrobenius_app_eq_algebraFrobenius]
  exact StandardFrobeniusPullback.canonicalConnection
    k Γ(X.scheme, U) M p

/-- The canonical connection on affine-local sections of mathlib's actual
Frobenius pullback, transported through `restrictedTopIso`. -/
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
/-- `restrictedTopIso` is horizontal for the canonical connections. -/
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
