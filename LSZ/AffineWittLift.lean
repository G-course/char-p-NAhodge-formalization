import LSZ.WittExact
import LSZ.AffineNilpotentLSZ
import LSZ.FiniteProjectiveDualBaseChange
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Smooth.Flat

/-!
# Affine Frobenius lifts and their divided differential

The input in this file is an actual smooth `W₂(k)`-algebra together with a
ring endomorphism lifting Frobenius.  No divided differential is supplied.
The first construction below proves that `d Φ` vanishes on the special
fibre, which makes the canonical division-by-`p` map from `WittExact`
applicable to Kähler differentials.
-/

open Function
open scoped TensorProduct

namespace LSZ

universe u

noncomputable section

namespace AffineWittLift

/-- A tagged copy of an `A`-module on which `a : A` acts through absolute
Frobenius, `m ↦ a ^ p • m`.  This is an internal device for applying the
ordinary Kähler universal property to a Frobenius-twisted derivation. -/
structure FrobeniusTwist (k : Type*) (A : Type*) (M : Type*) (p : ℕ) where
  down : M

namespace FrobeniusTwist

variable (k : Type*) (A : Type*) (M : Type*) (p : ℕ)

@[ext]
lemma ext {x y : FrobeniusTwist k A M p} (h : x.down = y.down) : x = y := by
  cases x
  cases y
  congr

/-- The underlying additive type of a Frobenius twist is unchanged. -/
def equiv : FrobeniusTwist k A M p ≃ M where
  toFun := down
  invFun := fun m ↦ ⟨m⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [AddCommGroup M] : AddCommGroup (FrobeniusTwist k A M p) :=
  (equiv k A M p).addCommGroup

variable [Field k] [CommRing A] [Algebra k A]
variable [CharP k p] [Fact p.Prime]
variable [AddCommGroup M] [Module A M]

instance : Module A (FrobeniusTwist k A M p) := by
  letI : Module A M := Module.compHom M (algebraFrobenius k A p)
  exact (equiv k A M p).module A

instance : Module k (FrobeniusTwist k A M p) :=
  Module.compHom (FrobeniusTwist k A M p) (algebraMap k A)

instance : IsScalarTower k A (FrobeniusTwist k A M p) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

@[simp]
lemma down_mk (m : M) : (FrobeniusTwist.mk m : FrobeniusTwist k A M p).down = m := rfl

@[simp]
lemma down_zero : (0 : FrobeniusTwist k A M p).down = 0 := by
  change (equiv k A M p) 0 = 0
  rw [Equiv.zero_def, Equiv.apply_symm_apply]

@[simp]
lemma down_add (x y : FrobeniusTwist k A M p) :
    (x + y).down = x.down + y.down := by
  change (equiv k A M p) (x + y) = _
  rw [Equiv.add_def, Equiv.apply_symm_apply]
  rfl

@[simp]
lemma down_smul (a : A) (x : FrobeniusTwist k A M p) :
    (a • x).down = algebraFrobenius k A p a • x.down := by
  change (equiv k A M p) (a • x) = _
  rw [Equiv.smul_def, Equiv.apply_symm_apply]
  rfl

end FrobeniusTwist

variable (p : ℕ) (k : Type u) (B : Type u)
variable [Field k] [CharP k p] [Fact p.Prime] [PerfectField k]
variable [CommRing B] [Algebra (W₂ p k) B]

/-- The canonical special-fibre algebra of a `W₂(k)`-algebra. -/
abbrev SpecialFiber := k ⊗[W₂ p k] B

/-- A Frobenius lift on a smooth affine `W₂(k)`-scheme.

`map_base` says that the endomorphism lies over Witt Frobenius.
`map_specialFiber` says on the canonical tensor-product special fibre that
it reduces to the absolute `p`-power Frobenius.  Neither field mentions a
divided differential or a connection. -/
structure Frobenius [Algebra.Smooth (W₂ p k) B] where
  map : B →+* B
  map_base (r : W₂ p k) :
    map (algebraMap (W₂ p k) B r) =
      algebraMap (W₂ p k) B (w₂Frobenius p k r)
  map_specialFiber (b : B) :
    (1 : k) ⊗ₜ[W₂ p k] map b =
      ((1 : k) ⊗ₜ[W₂ p k] b : SpecialFiber p k B) ^ p

variable [Algebra.Smooth (W₂ p k) B]

namespace Frobenius

variable (Phi : Frobenius p k B)

/-- The undivided differential `b ↦ d(Φ(b))`. -/
def rawDifferential : B →+ Ω[B⁄W₂ p k] where
  toFun b := KaehlerDifferential.D (W₂ p k) B (Phi.map b)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

@[simp]
lemma rawDifferential_apply (b : B) :
    rawDifferential p k B Phi b =
      KaehlerDifferential.D (W₂ p k) B (Phi.map b) := rfl

/-- The differential of a Frobenius lift vanishes after reduction to the
special fibre. -/
lemma toSpecialFiber_rawDifferential_eq_zero (b : B) :
    WittLengthTwo.toSpecialFiber p k (rawDifferential p k B Phi b) = 0 := by
  letI : Algebra B (SpecialFiber p k B) :=
    Algebra.TensorProduct.rightAlgebra
  let e := KaehlerDifferential.tensorKaehlerEquivBase
    (W₂ p k) k B (SpecialFiber p k B)
  apply e.injective
  rw [WittLengthTwo.toSpecialFiber_apply,
    KaehlerDifferential.tensorKaehlerEquivBase_tmul,
    one_smul, rawDifferential_apply,
    KaehlerDifferential.map_D, map_zero]
  change KaehlerDifferential.D k (SpecialFiber p k B)
      ((1 : k) ⊗ₜ[W₂ p k] Phi.map b) = 0
  rw [Phi.map_specialFiber b]
  rw [Derivation.leibniz_pow]
  have hpA : (p : SpecialFiber p k B) = 0 := by
    calc
      (p : SpecialFiber p k B) =
          algebraMap k (SpecialFiber p k B) (p : k) :=
        (map_natCast (algebraMap k (SpecialFiber p k B)) p).symm
      _ = algebraMap k (SpecialFiber p k B) 0 := by
        rw [CharP.cast_eq_zero]
      _ = 0 := map_zero _
  rw [← Nat.cast_smul_eq_nsmul (SpecialFiber p k B), hpA,
    zero_smul]

/-- For a smooth lift, the relative Kähler differentials are flat over
`W₂(k)`.  This is the composite of projectivity over `B` and smooth
flatness of `B` over `W₂(k)`. -/
lemma kaehlerDifferential_flat :
    Module.Flat (W₂ p k) Ω[B⁄W₂ p k] :=
  Module.Flat.trans (W₂ p k) B Ω[B⁄W₂ p k]

/-- The differential `d Φ` regarded as an element of the kernel of
reduction to the special fibre. -/
def rawDifferentialKernel :
    B →+ LinearMap.ker
      (WittLengthTwo.toSpecialFiber
        (M := Ω[B⁄W₂ p k]) p k) where
  toFun b := ⟨rawDifferential p k B Phi b,
    toSpecialFiber_rawDifferential_eq_zero p k B Phi b⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (rawDifferential p k B Phi)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (rawDifferential p k B Phi) x y

/-- The canonical divided differential of the Frobenius lift, before the
standard base-change identification of Kähler differentials.  It is obtained
by dividing `d Φ` by `p` and reducing; no divided differential is part of
the input. -/
noncomputable def dividedDifferential :
    B →+ k ⊗[W₂ p k] Ω[B⁄W₂ p k] := by
  letI : Module.Flat (W₂ p k) Ω[B⁄W₂ p k] :=
    kaehlerDifferential_flat p k B
  exact (WittLengthTwo.divideByP
    (M := Ω[B⁄W₂ p k]) p k).toAddMonoidHom.comp
      (rawDifferentialKernel p k B Phi)

/-- The differential of the Frobenius lift commutes with multiplication by
`p`.  This uses that Witt Frobenius fixes the natural-number element `p`. -/
lemma rawDifferential_p_smul (b : B) :
    rawDifferential p k B Phi ((p : W₂ p k) • b) =
      (p : W₂ p k) • rawDifferential p k B Phi b := by
  rw [Algebra.smul_def, rawDifferential_apply, map_mul, Phi.map_base,
    map_natCast, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero]
  exact algebraMap_smul B (p : W₂ p k)
    (rawDifferential p k B Phi b)

/-- Product rule for the undivided differential of the Frobenius lift. -/
lemma rawDifferential_mul (x y : B) :
    rawDifferential p k B Phi (x * y) =
      Phi.map x • rawDifferential p k B Phi y +
        Phi.map y • rawDifferential p k B Phi x := by
  rw [rawDifferential_apply, map_mul, Derivation.leibniz,
    ← rawDifferential_apply, ← rawDifferential_apply]

/-- The relative differential of the Frobenius lift vanishes on base
coefficients. -/
lemma rawDifferential_algebraMap (r : W₂ p k) :
    rawDifferential p k B Phi (algebraMap (W₂ p k) B r) = 0 := by
  rw [rawDifferential_apply, Phi.map_base,
    Derivation.map_algebraMap]

/-- Characterizing formula for the divided differential. -/
lemma dividedDifferential_eq_of_rawDifferential_eq_p_smul
    (b : B) (omega : Ω[B⁄W₂ p k])
    (h : rawDifferential p k B Phi b = (p : W₂ p k) • omega) :
    dividedDifferential p k B Phi b =
      WittLengthTwo.toSpecialFiber p k omega := by
  letI : Module.Flat (W₂ p k) Ω[B⁄W₂ p k] :=
    kaehlerDifferential_flat p k B
  change WittLengthTwo.divideByP p k
      (rawDifferentialKernel p k B Phi b) = _
  exact WittLengthTwo.divideByP_eq_of_eq_p_smul p k
    (rawDifferentialKernel p k B Phi b) omega h

/-- Multiplying a lift by `p` does not change the descended divided
differential: its value is zero on the special fibre. -/
lemma dividedDifferential_p_smul (b : B) :
    dividedDifferential p k B Phi ((p : W₂ p k) • b) = 0 := by
  calc
    dividedDifferential p k B Phi ((p : W₂ p k) • b) =
        WittLengthTwo.toSpecialFiber p k
          (rawDifferential p k B Phi b) :=
      dividedDifferential_eq_of_rawDifferential_eq_p_smul p k B Phi
        ((p : W₂ p k) • b) (rawDifferential p k B Phi b)
        (rawDifferential_p_smul p k B Phi b)
    _ = 0 := toSpecialFiber_rawDifferential_eq_zero p k B Phi b

/-- The divided differential vanishes on base coefficients. -/
lemma dividedDifferential_algebraMap (r : W₂ p k) :
    dividedDifferential p k B Phi (algebraMap (W₂ p k) B r) = 0 := by
  calc
    dividedDifferential p k B Phi (algebraMap (W₂ p k) B r) =
        WittLengthTwo.toSpecialFiber p k (0 : Ω[B⁄W₂ p k]) :=
      dividedDifferential_eq_of_rawDifferential_eq_p_smul p k B Phi
        (algebraMap (W₂ p k) B r) 0 (by
          rw [rawDifferential_algebraMap, smul_zero])
    _ = 0 := map_zero (WittLengthTwo.toSpecialFiber
      (M := Ω[B⁄W₂ p k]) p k)

/-- The canonical map from a lift to its special fibre is surjective. -/
lemma toSpecialFiber_surjective :
    Function.Surjective
      (WittLengthTwo.toSpecialFiber (M := B) p k) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      exact ⟨0, map_zero (WittLengthTwo.toSpecialFiber (M := B) p k)⟩
  | tmul a b =>
      obtain ⟨r, hr⟩ := w₂Reduction_surjective p k a
      refine ⟨r • b, ?_⟩
      rw [WittLengthTwo.toSpecialFiber_apply, TensorProduct.tmul_smul]
      change (w₂Reduction p k r • (1 : k)) ⊗ₜ[W₂ p k] b = a ⊗ₜ[W₂ p k] b
      rw [hr, smul_eq_mul, mul_one]
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' + y', ?_⟩
      rw [map_add, hx', hy']

/-- The canonical special-fibre map preserves multiplication. -/
@[simp]
lemma toSpecialFiber_mul (x y : B) :
    WittLengthTwo.toSpecialFiber p k (x * y) =
      WittLengthTwo.toSpecialFiber p k x *
        WittLengthTwo.toSpecialFiber p k y := by
  rw [WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Reduction of a base coefficient agrees with the left `k`-algebra
structure on the tensor-product special fibre. -/
lemma toSpecialFiber_algebraMap (r : W₂ p k) :
    WittLengthTwo.toSpecialFiber p k (algebraMap (W₂ p k) B r) =
      algebraMap k (SpecialFiber p k B) (w₂Reduction p k r) := by
  rw [WittLengthTwo.toSpecialFiber_apply]
  change (1 : k) ⊗ₜ[W₂ p k] algebraMap (W₂ p k) B r =
    (w₂Reduction p k r) ⊗ₜ[W₂ p k] (1 : B)
  calc
    (1 : k) ⊗ₜ[W₂ p k] algebraMap (W₂ p k) B r =
        (1 : k) ⊗ₜ[W₂ p k] ((r : W₂ p k) • (1 : B)) := by
      rw [Algebra.smul_def, mul_one]
    _ = ((r : W₂ p k) • (1 : k)) ⊗ₜ[W₂ p k] (1 : B) :=
      TensorProduct.tmul_smul _ _ _
    _ = (w₂Reduction p k r) ⊗ₜ[W₂ p k] (1 : B) := by
      rw [Algebra.smul_def, mul_one,
        WittLengthTwo.algebraMap_residue_apply]

/-- The divided differential depends only on the image of a lift in the
special fibre. -/
lemma dividedDifferential_eq_of_toSpecialFiber_eq {x y : B}
    (h : WittLengthTwo.toSpecialFiber p k x =
      WittLengthTwo.toSpecialFiber p k y) :
    dividedDifferential p k B Phi x =
      dividedDifferential p k B Phi y := by
  have hzero : WittLengthTwo.toSpecialFiber p k (x - y) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨z, hz⟩ :=
    WittLengthTwo.exists_eq_p_smul_of_toSpecialFiber_eq_zero
      p k (x - y) hzero
  apply sub_eq_zero.mp
  rw [← map_sub, hz, dividedDifferential_p_smul]

/-- A chosen lift of a special-fibre element.  All public constructions below
are independent of this choice. -/
private noncomputable def specialFiberLift
    (a : SpecialFiber p k B) : B :=
  (toSpecialFiber_surjective p k B a).choose

private lemma toSpecialFiber_specialFiberLift
    (a : SpecialFiber p k B) :
    WittLengthTwo.toSpecialFiber p k (specialFiberLift p k B a) = a :=
  (toSpecialFiber_surjective p k B a).choose_spec

/-- The divided differential descended canonically from the lift `B` to its
special fibre. -/
noncomputable def specialFiberDividedDifferential :
    SpecialFiber p k B →+
      k ⊗[W₂ p k] Ω[B⁄W₂ p k] where
  toFun a := dividedDifferential p k B Phi (specialFiberLift p k B a)
  map_zero' := by
    rw [← map_zero (dividedDifferential p k B Phi)]
    apply dividedDifferential_eq_of_toSpecialFiber_eq p k B Phi
    rw [toSpecialFiber_specialFiberLift, map_zero]
  map_add' a b := by
    rw [← map_add (dividedDifferential p k B Phi)]
    apply dividedDifferential_eq_of_toSpecialFiber_eq p k B Phi
    rw [toSpecialFiber_specialFiberLift, map_add,
      toSpecialFiber_specialFiberLift, toSpecialFiber_specialFiberLift]

/-- Formula for the descended divided differential on an element represented
by `b : B`. -/
@[simp]
lemma specialFiberDividedDifferential_toSpecialFiber (b : B) :
    specialFiberDividedDifferential p k B Phi
        (WittLengthTwo.toSpecialFiber p k b) =
      dividedDifferential p k B Phi b := by
  apply dividedDifferential_eq_of_toSpecialFiber_eq p k B Phi
  exact toSpecialFiber_specialFiberLift p k B
    (WittLengthTwo.toSpecialFiber p k b)

/-- The standard base-change identification
`k ⊗[W₂(k)] Ω[B/W₂(k)] ≃ Ω[(k ⊗[W₂(k)] B)/k]`. -/
noncomputable def specialFiberKaehlerEquiv :
    (k ⊗[W₂ p k] Ω[B⁄W₂ p k]) ≃ₗ[k]
      Ω[SpecialFiber p k B⁄k] := by
  letI : Algebra B (SpecialFiber p k B) :=
    Algebra.TensorProduct.rightAlgebra
  exact KaehlerDifferential.tensorKaehlerEquivBase
    (W₂ p k) k B (SpecialFiber p k B)

/-- The descended divided differential with values in the actual Kähler
differentials of the special fibre. -/
noncomputable def specialFiberDividedDifferentialForm :
    SpecialFiber p k B →+ Ω[SpecialFiber p k B⁄k] :=
  (specialFiberKaehlerEquiv p k B).toLinearMap.toAddMonoidHom.comp
    (specialFiberDividedDifferential p k B Phi)

/-- Generator formula for the special-fibre divided differential form. -/
@[simp]
lemma specialFiberDividedDifferentialForm_toSpecialFiber (b : B) :
    specialFiberDividedDifferentialForm p k B Phi
        (WittLengthTwo.toSpecialFiber p k b) =
      specialFiberKaehlerEquiv p k B
        (dividedDifferential p k B Phi b) := by
  change specialFiberKaehlerEquiv p k B
      (specialFiberDividedDifferential p k B Phi
        (WittLengthTwo.toSpecialFiber p k b)) = _
  rw [specialFiberDividedDifferential_toSpecialFiber]

/-- Base change carries multiplication by a coefficient of `B` to
multiplication by its image in the special fibre. -/
lemma specialFiberKaehlerEquiv_toSpecialFiber_smul
    (b : B) (omega : Ω[B⁄W₂ p k]) :
    specialFiberKaehlerEquiv p k B
        (WittLengthTwo.toSpecialFiber p k (b • omega)) =
      WittLengthTwo.toSpecialFiber p k b •
        specialFiberKaehlerEquiv p k B
          (WittLengthTwo.toSpecialFiber p k omega) := by
  letI : Algebra B (SpecialFiber p k B) :=
    Algebra.TensorProduct.rightAlgebra
  rw [WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply]
  change KaehlerDifferential.tensorKaehlerEquivBase
      (W₂ p k) k B (SpecialFiber p k B)
        ((1 : k) ⊗ₜ[W₂ p k] (b • omega)) =
    ((1 : k) ⊗ₜ[W₂ p k] b) •
      KaehlerDifferential.tensorKaehlerEquivBase
        (W₂ p k) k B (SpecialFiber p k B)
          ((1 : k) ⊗ₜ[W₂ p k] omega)
  rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul,
    KaehlerDifferential.tensorKaehlerEquivBase_tmul,
    one_smul, one_smul, map_smul]
  rfl

/-- The chosen Frobenius lift reduces to absolute Frobenius under the
canonical special-fibre map. -/
lemma toSpecialFiber_map_eq_pow (b : B) :
    WittLengthTwo.toSpecialFiber p k (Phi.map b) =
      (WittLengthTwo.toSpecialFiber p k b) ^ p := by
  rw [WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply]
  exact Phi.map_specialFiber b

/-- On elements represented by the lift, the divided differential satisfies
the Frobenius-twisted Leibniz rule. -/
lemma specialFiberKaehlerEquiv_dividedDifferential_mul (x y : B) :
    specialFiberKaehlerEquiv p k B
        (dividedDifferential p k B Phi (x * y)) =
      (WittLengthTwo.toSpecialFiber p k x) ^ p •
          specialFiberKaehlerEquiv p k B
            (dividedDifferential p k B Phi y) +
        (WittLengthTwo.toSpecialFiber p k y) ^ p •
          specialFiberKaehlerEquiv p k B
            (dividedDifferential p k B Phi x) := by
  letI : Module.Flat (W₂ p k) Ω[B⁄W₂ p k] :=
    kaehlerDifferential_flat p k B
  obtain ⟨dx, hdx⟩ :=
    WittLengthTwo.exists_eq_p_smul_of_toSpecialFiber_eq_zero
      p k (rawDifferential p k B Phi x)
        (toSpecialFiber_rawDifferential_eq_zero p k B Phi x)
  obtain ⟨dy, hdy⟩ :=
    WittLengthTwo.exists_eq_p_smul_of_toSpecialFiber_eq_zero
      p k (rawDifferential p k B Phi y)
        (toSpecialFiber_rawDifferential_eq_zero p k B Phi y)
  have hxy : rawDifferential p k B Phi (x * y) =
      (p : W₂ p k) • (Phi.map x • dy + Phi.map y • dx) := by
    calc
      rawDifferential p k B Phi (x * y) =
          Phi.map x • rawDifferential p k B Phi y +
            Phi.map y • rawDifferential p k B Phi x :=
        rawDifferential_mul p k B Phi x y
      _ = Phi.map x • ((p : W₂ p k) • dy) +
          Phi.map y • ((p : W₂ p k) • dx) := by
        rw [hdy, hdx]
      _ = (p : W₂ p k) • (Phi.map x • dy + Phi.map y • dx) := by
        rw [smul_comm (Phi.map x) (p : W₂ p k) dy,
          smul_comm (Phi.map y) (p : W₂ p k) dx, smul_add]
  rw [dividedDifferential_eq_of_rawDifferential_eq_p_smul
    p k B Phi (x * y) (Phi.map x • dy + Phi.map y • dx) hxy]
  rw [map_add (WittLengthTwo.toSpecialFiber
      (M := Ω[B⁄W₂ p k]) p k),
    map_add (specialFiberKaehlerEquiv p k B)]
  rw [specialFiberKaehlerEquiv_toSpecialFiber_smul,
    specialFiberKaehlerEquiv_toSpecialFiber_smul]
  rw [← dividedDifferential_eq_of_rawDifferential_eq_p_smul
      p k B Phi y dy hdy,
    ← dividedDifferential_eq_of_rawDifferential_eq_p_smul
      p k B Phi x dx hdx,
    toSpecialFiber_map_eq_pow, toSpecialFiber_map_eq_pow]

/-- The descended form is a Frobenius-twisted derivation on the entire
special fibre. -/
lemma specialFiberDividedDifferentialForm_leibniz
    (a b : SpecialFiber p k B) :
    specialFiberDividedDifferentialForm p k B Phi (a * b) =
      a ^ p • specialFiberDividedDifferentialForm p k B Phi b +
        b ^ p • specialFiberDividedDifferentialForm p k B Phi a := by
  obtain ⟨x, rfl⟩ := toSpecialFiber_surjective p k B a
  obtain ⟨y, rfl⟩ := toSpecialFiber_surjective p k B b
  rw [← toSpecialFiber_mul,
    specialFiberDividedDifferentialForm_toSpecialFiber,
    specialFiberDividedDifferentialForm_toSpecialFiber,
    specialFiberDividedDifferentialForm_toSpecialFiber]
  exact specialFiberKaehlerEquiv_dividedDifferential_mul p k B Phi x y

/-- The descended divided differential kills the image of the base field. -/
lemma specialFiberDividedDifferentialForm_algebraMap (c : k) :
    specialFiberDividedDifferentialForm p k B Phi
        (algebraMap k (SpecialFiber p k B) c) = 0 := by
  obtain ⟨r, hr⟩ := w₂Reduction_surjective p k c
  have hbase :
      WittLengthTwo.toSpecialFiber p k
          (algebraMap (W₂ p k) B r) =
        algebraMap k (SpecialFiber p k B) c := by
    rw [toSpecialFiber_algebraMap, hr]
  rw [← hbase, specialFiberDividedDifferentialForm_toSpecialFiber,
    dividedDifferential_algebraMap, map_zero]

/-- `k`-semilinearity of the divided differential, written in the ordinary
cotangent module. -/
lemma specialFiberDividedDifferentialForm_smul (c : k)
    (a : SpecialFiber p k B) :
    specialFiberDividedDifferentialForm p k B Phi (c • a) =
      (algebraMap k (SpecialFiber p k B) c) ^ p •
        specialFiberDividedDifferentialForm p k B Phi a := by
  rw [Algebra.smul_def,
    specialFiberDividedDifferentialForm_leibniz,
    specialFiberDividedDifferentialForm_algebraMap,
    smul_zero, add_zero]

/-- The divided differential as an ordinary derivation into the
Frobenius-twisted cotangent module. -/
noncomputable def frobeniusTwistedDerivation :
    Derivation k (SpecialFiber p k B)
      (FrobeniusTwist k (SpecialFiber p k B)
        Ω[SpecialFiber p k B⁄k] p) where
  toLinearMap :=
    { toFun := fun a ↦
        FrobeniusTwist.mk
          (specialFiberDividedDifferentialForm p k B Phi a)
      map_add' := by
        intro a b
        apply FrobeniusTwist.ext
        change specialFiberDividedDifferentialForm p k B Phi (a + b) = _
        rw [FrobeniusTwist.down_add, FrobeniusTwist.down_mk,
          FrobeniusTwist.down_mk]
        exact map_add (specialFiberDividedDifferentialForm p k B Phi) a b
      map_smul' := by
        intro c a
        apply FrobeniusTwist.ext
        change specialFiberDividedDifferentialForm p k B Phi (c • a) =
          algebraFrobenius k (SpecialFiber p k B) p
              (algebraMap k (SpecialFiber p k B) c) •
            specialFiberDividedDifferentialForm p k B Phi a
        rw [algebraFrobenius_apply]
        exact specialFiberDividedDifferentialForm_smul p k B Phi c a }
  map_one_eq_zero' := by
    apply FrobeniusTwist.ext
    change specialFiberDividedDifferentialForm p k B Phi 1 = 0
    have h := specialFiberDividedDifferentialForm_algebraMap
      p k B Phi (1 : k)
    rw [map_one] at h
    exact h
  leibniz' := by
    intro a b
    apply FrobeniusTwist.ext
    change specialFiberDividedDifferentialForm p k B Phi (a * b) = _
    rw [FrobeniusTwist.down_add,
      FrobeniusTwist.down_smul, FrobeniusTwist.down_smul,
      FrobeniusTwist.down_mk, FrobeniusTwist.down_mk,
      algebraFrobenius_apply, algebraFrobenius_apply]
    exact specialFiberDividedDifferentialForm_leibniz p k B Phi a b

/-- The map on Kähler differentials supplied by their universal property,
with Frobenius twist retained in the codomain. -/
noncomputable def twistedCotangentLinearMap :
    Ω[SpecialFiber p k B⁄k] →ₗ[SpecialFiber p k B]
      FrobeniusTwist k (SpecialFiber p k B)
        Ω[SpecialFiber p k B⁄k] p :=
  (frobeniusTwistedDerivation p k B Phi).liftKaehlerDifferential

/-- Formula for the twisted cotangent map on universal differentials. -/
@[simp]
lemma twistedCotangentLinearMap_D (a : SpecialFiber p k B) :
    twistedCotangentLinearMap p k B Phi
        (KaehlerDifferential.D k (SpecialFiber p k B) a) =
      FrobeniusTwist.mk
        (specialFiberDividedDifferentialForm p k B Phi a) :=
  Derivation.liftKaehlerDifferential_comp_D
    (frobeniusTwistedDerivation p k B Phi) a

/-- The divided Frobenius differential as a semilinear map
`Ω[A/k] →ₛₗ[F_A] Ω[A/k]`. -/
noncomputable def cotangentSemilinear :
    Ω[SpecialFiber p k B⁄k] →ₛₗ[
      algebraFrobenius k (SpecialFiber p k B) p]
        Ω[SpecialFiber p k B⁄k] where
  toFun omega := (twistedCotangentLinearMap p k B Phi omega).down
  map_add' x y := by
    have h := congrArg FrobeniusTwist.down
      (map_add (twistedCotangentLinearMap p k B Phi) x y)
    rw [FrobeniusTwist.down_add] at h
    exact h
  map_smul' a x := by
    have h := congrArg FrobeniusTwist.down
      (map_smul (twistedCotangentLinearMap p k B Phi) a x)
    rw [FrobeniusTwist.down_smul] at h
    exact h

/-- Generator formula for the semilinear cotangent map. -/
@[simp]
lemma cotangentSemilinear_D (a : SpecialFiber p k B) :
    cotangentSemilinear p k B Phi
        (KaehlerDifferential.D k (SpecialFiber p k B) a) =
      specialFiberDividedDifferentialForm p k B Phi a := by
  change (twistedCotangentLinearMap p k B Phi
    (KaehlerDifferential.D k (SpecialFiber p k B) a)).down = _
  rw [twistedCotangentLinearMap_D, FrobeniusTwist.down_mk]

/-- The semilinear cotangent map as a morphism into mathlib's restriction of
scalars.  This is the component before applying the extension--restriction
adjunction. -/
noncomputable def cotangentUnit :
    ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] ⟶
      (ModuleCat.restrictScalars
        (algebraFrobenius k (SpecialFiber p k B) p)).obj
          (ModuleCat.of (SpecialFiber p k B)
            Ω[SpecialFiber p k B⁄k]) :=
  ModuleCat.semilinearMapAddEquiv
    (algebraFrobenius k (SpecialFiber p k B) p)
    (ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])
    (ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])
      (cotangentSemilinear p k B Phi)

/-- The actual divided Frobenius map on cotangent modules,
`F_A^* Ω[A/k] → Ω[A/k]`, in mathlib's standard extension-of-scalars
model. -/
noncomputable def dividedFrobeniusCotangentHom :
    (ModuleCat.extendScalars
      (algebraFrobenius k (SpecialFiber p k B) p)).obj
        (ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k]) ⟶
      ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] :=
  (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
    (algebraFrobenius k (SpecialFiber p k B) p)).symm
      (cotangentUnit p k B Phi)

/-- The divided Frobenius cotangent morphism as an `A`-linear map. -/
abbrev dividedFrobeniusCotangent :
    (ModuleCat.extendScalars
      (algebraFrobenius k (SpecialFiber p k B) p)).obj
        (ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k]) →ₗ[
          SpecialFiber p k B] Ω[SpecialFiber p k B⁄k] :=
  (dividedFrobeniusCotangentHom p k B Phi).hom

/-- Formula for `d Phi / p` on a pulled-back universal differential. -/
@[simp]
lemma dividedFrobeniusCotangent_tmul_D
    (a b : SpecialFiber p k B) :
    dividedFrobeniusCotangent p k B Phi
        (StandardFrobeniusPullback.tmul k (SpecialFiber p k B)
          Ω[SpecialFiber p k B⁄k] p a
            (KaehlerDifferential.D k (SpecialFiber p k B) b)) =
      a • specialFiberDividedDifferentialForm p k B Phi b := by
  let d := KaehlerDifferential.D k (SpecialFiber p k B) b
  have hunit :
      (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
        (algebraFrobenius k (SpecialFiber p k B) p))
          (dividedFrobeniusCotangentHom p k B Phi) =
        cotangentUnit p k B Phi := by
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
      (algebraFrobenius k (SpecialFiber p k B) p)).apply_symm_apply
        (cotangentUnit p k B Phi)
  have hone : dividedFrobeniusCotangent p k B Phi
      (StandardFrobeniusPullback.tmul k (SpecialFiber p k B)
        Ω[SpecialFiber p k B⁄k] p 1 d) =
        cotangentSemilinear p k B Phi d := by
    have hunit' :
        (ModuleCat.extendRestrictScalarsAdj
          (algebraFrobenius k (SpecialFiber p k B) p)).homEquiv _ _
            (dividedFrobeniusCotangentHom p k B Phi) =
          cotangentUnit p k B Phi := by
      change (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
        (algebraFrobenius k (SpecialFiber p k B) p))
          (dividedFrobeniusCotangentHom p k B Phi) = _
      exact hunit
    have h := congrArg
      (fun q ↦ q.hom d) hunit'
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at h
    change dividedFrobeniusCotangent p k B Phi
        (StandardFrobeniusPullback.tmul k (SpecialFiber p k B)
          Ω[SpecialFiber p k B⁄k] p 1 d) =
      cotangentSemilinear p k B Phi d at h
    exact h
  have htmul : StandardFrobeniusPullback.tmul k (SpecialFiber p k B)
      Ω[SpecialFiber p k B⁄k] p a d =
        a • StandardFrobeniusPullback.tmul k (SpecialFiber p k B)
          Ω[SpecialFiber p k B⁄k] p 1 d := by
    have h := ModuleCat.ExtendScalars.smul_tmul
      (M := ModuleCat.of (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])
      (algebraFrobenius k (SpecialFiber p k B) p) a 1 d
    rw [mul_one] at h
    exact h.symm
  rw [htmul, map_smul, hone]
  exact congrArg (fun omega ↦ a • omega)
    (cotangentSemilinear_D p k B Phi b)

/-- The standard identification of tangent derivations with the dual of
Kähler differentials. -/
noncomputable def cotangentDualEquivTangent :
    Module.Dual (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] ≃ₗ[
      SpecialFiber p k B] Tangent k (SpecialFiber p k B) :=
  KaehlerDifferential.linearMapEquivDerivation k (SpecialFiber p k B)

/-- Finite projectivity of the cotangent module identifies the Frobenius
pullback of its dual with the dual of its Frobenius pullback. -/
noncomputable def frobeniusDualBaseChangeEquiv :
    AffineFrobeniusLift.pullback k (SpecialFiber p k B) p
        (ModuleCat.of (SpecialFiber p k B) (Module.Dual
          (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])) ≃ₗ[
      SpecialFiber p k B]
      Module.Dual (SpecialFiber p k B)
        (AffineFrobeniusLift.pullback k (SpecialFiber p k B) p
          (ModuleCat.of (SpecialFiber p k B)
            Ω[SpecialFiber p k B⁄k])) := by
  letI smoothSpecialFiber : Algebra.Smooth k (SpecialFiber p k B) :=
    Algebra.Smooth.baseChange (W₂ p k) B k
  let cotangentModule :
      Module (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] :=
    inferInstance
  let cotangentAddCommGroup :
      AddCommGroup Ω[SpecialFiber p k B⁄k] :=
    inferInstance
  let dualModule : Module (SpecialFiber p k B)
      (Module.Dual (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k]) :=
    inferInstance
  let dualAddCommGroup : AddCommGroup
      (Module.Dual (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k]) :=
    inferInstance
  letI finiteCotangent :
      Module.Finite (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] := by
    infer_instance
  letI projectiveCotangent :
      Module.Projective (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] := by
    infer_instance
  let frobeniusAlgebra :
      Algebra (SpecialFiber p k B) (SpecialFiber p k B) :=
    (algebraFrobenius k (SpecialFiber p k B) p).toAlgebra
  let regularModule :
      Module (SpecialFiber p k B) (SpecialFiber p k B) :=
    Semiring.toModule
  let frobeniusSourceModule :
      Module (SpecialFiber p k B) (SpecialFiber p k B) :=
    @Algebra.toModule (SpecialFiber p k B) (SpecialFiber p k B)
      _ _ frobeniusAlgebra
  let commutingActions : @SMulCommClass
      (SpecialFiber p k B) (SpecialFiber p k B) (SpecialFiber p k B)
      frobeniusSourceModule.toSMul regularModule.toSMul := by
    exact @SMulCommClass.mk
      (SpecialFiber p k B) (SpecialFiber p k B) (SpecialFiber p k B)
      frobeniusSourceModule.toSMul regularModule.toSMul (fun r s x ↦ by
        change (algebraFrobenius k (SpecialFiber p k B) p) r * (s * x) =
          s * ((algebraFrobenius k (SpecialFiber p k B) p) r * x)
        calc
          _ = ((algebraFrobenius k (SpecialFiber p k B) p) r * s) * x :=
            (mul_assoc _ _ _).symm
          _ = (s * (algebraFrobenius k (SpecialFiber p k B) p) r) * x := by
            rw [mul_comm ((algebraFrobenius k
              (SpecialFiber p k B) p) r) s]
          _ = _ := mul_assoc _ _ _)
  let eDual := @FiniteProjectiveDualBaseChange.extensionTensorEquiv
    (SpecialFiber p k B) (SpecialFiber p k B) _ _ frobeniusAlgebra
    (Module.Dual (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])
    dualAddCommGroup dualModule
  let eOmega := @FiniteProjectiveDualBaseChange.extensionTensorEquiv
    (SpecialFiber p k B) (SpecialFiber p k B) _ _ frobeniusAlgebra
    Ω[SpecialFiber p k B⁄k] cotangentAddCommGroup cotangentModule
  let tensorTargetModule := @TensorProduct.leftModule
    (SpecialFiber p k B) (SpecialFiber p k B) _ _
    (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k] _ _
    regularModule frobeniusSourceModule cotangentModule commutingActions
  let eOmegaDual := @Module.Dual.congr (SpecialFiber p k B) _
    _ _ _ _ _ tensorTargetModule eOmega
  exact eDual.trans (((@FiniteProjectiveDualBaseChange.equiv
    (SpecialFiber p k B) (SpecialFiber p k B) _ _ frobeniusAlgebra
    Ω[SpecialFiber p k B⁄k] cotangentAddCommGroup cotangentModule
    finiteCotangent projectiveCotangent)).trans
      eOmegaDual.symm)

/-- Base change of the cotangent-dual--tangent identification. -/
noncomputable def pullbackCotangentDualEquivTangent :
    AffineFrobeniusLift.pullback k (SpecialFiber p k B) p
        (ModuleCat.of (SpecialFiber p k B) (Module.Dual
          (SpecialFiber p k B) Ω[SpecialFiber p k B⁄k])) ≃ₗ[
      SpecialFiber p k B]
      AffineFrobeniusLift.pullback k (SpecialFiber p k B) p
        (AffineFrobeniusLift.tangentModule k (SpecialFiber p k B)) := by
  exact ((ModuleCat.extendScalars
    (algebraFrobenius k (SpecialFiber p k B) p)).mapIso
      (cotangentDualEquivTangent p k B).toModuleIso).toLinearEquiv

/-- The dual divided Frobenius map
`T_A → F_A^* T_A` obtained from the actual Frobenius lift. -/
noncomputable def dividedFrobeniusZeta :
    Tangent k (SpecialFiber p k B) →ₗ[SpecialFiber p k B]
      AffineFrobeniusLift.pullback k (SpecialFiber p k B) p
        (AffineFrobeniusLift.tangentModule k (SpecialFiber p k B)) :=
  (pullbackCotangentDualEquivTangent p k B).toLinearMap.comp
    ((frobeniusDualBaseChangeEquiv p k B).symm.toLinearMap.comp
      ((dividedFrobeniusCotangent p k B Phi).dualMap.comp
        (cotangentDualEquivTangent p k B).symm.toLinearMap))

end Frobenius

end AffineWittLift

end

end LSZ
