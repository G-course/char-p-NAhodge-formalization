import LSZ.WittLift
import Mathlib.RingTheory.Flat.Basic

/-!
# The square-zero Witt extension and flat base change

This file isolates the algebraic division-by-`p` fact used by the divided
differential.  For a perfect field `k`, the sequence

`W₂(k) --(* p)--> W₂(k) --> k`

is exact in the middle.  Tensoring it with a flat `W₂(k)`-module preserves
exactness.  Thus an element of a smooth lift whose special-fibre image is
zero is a multiple of `p`; no choice of a division operation is included in
the input data.
-/

open Function
open scoped TensorProduct

namespace LSZ

universe u v

noncomputable section

namespace WittLengthTwo

variable (p : ℕ) (k : Type u)
variable [Field k] [CharP k p] [Fact p.Prime]

/-- The canonical `W₂(k)`-algebra structure on its residue field. -/
noncomputable instance residueAlgebra : Algebra (W₂ p k) k :=
  (w₂Reduction p k).toAlgebra

@[simp]
lemma algebraMap_residue_apply (x : W₂ p k) :
    algebraMap (W₂ p k) k x = w₂Reduction p k x := rfl

/-- Multiplication by `p` as a `W₂(k)`-linear map. -/
def mulP : W₂ p k →ₗ[W₂ p k] W₂ p k where
  toFun x := x * p
  map_add' x y := add_mul x y p
  map_smul' a x := by
    change (a * x) * p = a * (x * p)
    rw [mul_assoc]

@[simp]
lemma mulP_apply (x : W₂ p k) : mulP p k x = x * p := rfl

/-- Reduction to the residue field as a `W₂(k)`-linear map. -/
def reductionLinear : W₂ p k →ₗ[W₂ p k] k :=
  Algebra.linearMap (W₂ p k) k

@[simp]
lemma reductionLinear_apply (x : W₂ p k) :
    reductionLinear p k x = w₂Reduction p k x := rfl

/-- Exactness of `W₂(k) --(* p)--> W₂(k) --> k` at the middle term. -/
lemma exact_mulP_reduction [PerfectField k] :
    Exact (mulP p k) (reductionLinear p k) := by
  rw [LinearMap.exact_iff]
  ext x
  change w₂Reduction p k x = 0 ↔ ∃ y, y * p = x
  rw [w₂Reduction_eq_zero_iff_exists_mul_p]
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩

/-- Exactness of multiplication by `p` followed by multiplication by `p`.
For length two this is the equality `ann(p) = (p)`. -/
lemma exact_mulP_mulP [PerfectField k] :
    Exact (mulP p k) (mulP p k) := by
  rw [LinearMap.exact_iff]
  ext x
  change x * p = 0 ↔ ∃ y, y * p = x
  rw [w₂_mul_p_eq_zero_iff_reduction_eq_zero,
    w₂Reduction_eq_zero_iff_exists_mul_p]
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩

variable {M : Type v} [AddCommGroup M] [Module (W₂ p k) M]

/-- The underlying module map from a lift to its tensor-product special
fibre, `m ↦ 1 ⊗ m`. -/
def toSpecialFiber : M →ₗ[W₂ p k] k ⊗[W₂ p k] M :=
  ((reductionLinear p k).rTensor M).comp
    (TensorProduct.lid (W₂ p k) M).symm.toLinearMap

@[simp]
lemma toSpecialFiber_apply (m : M) :
    toSpecialFiber p k m = (1 : k) ⊗ₜ[W₂ p k] m := by
  change (reductionLinear p k).rTensor M
      ((TensorProduct.lid (W₂ p k) M).symm m) = _
  rw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
  have hone : reductionLinear p k (1 : W₂ p k) = 1 := by
    change w₂Reduction p k 1 = 1
    exact map_one (w₂Reduction p k)
  rw [hone]

private lemma lid_rTensor_mulP (z : W₂ p k ⊗[W₂ p k] M) :
    TensorProduct.lid (W₂ p k) M ((mulP p k).rTensor M z) =
      (p : W₂ p k) • TensorProduct.lid (W₂ p k) M z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, smul_zero]
  | tmul r b =>
      rw [LinearMap.rTensor_tmul, mulP_apply,
        TensorProduct.lid_tmul, TensorProduct.lid_tmul, smul_smul]
      change (r * p) • b = (p * r) • b
      rw [mul_comm]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, smul_add]

/-- Flatness preserves the elementary division-by-`p` statement: if the
canonical image of `b` in `k ⊗_{W₂(k)} B` vanishes, then `b = p b'` for
some `b'`. -/
lemma exists_eq_p_smul_of_toSpecialFiber_eq_zero [PerfectField k]
    [Module.Flat (W₂ p k) M] (m : M)
    (hm : toSpecialFiber p k m = 0) :
    ∃ m' : M, m = (p : W₂ p k) • m' := by
  let x : W₂ p k ⊗[W₂ p k] M :=
    (TensorProduct.lid (W₂ p k) M).symm m
  have hx : (reductionLinear p k).rTensor M x = 0 := by
    exact hm
  have hexact : Exact
      ((mulP p k).rTensor M) ((reductionLinear p k).rTensor M) :=
    Module.Flat.rTensor_exact M (exact_mulP_reduction p k)
  have hxker : x ∈ LinearMap.ker ((reductionLinear p k).rTensor M) := hx
  have hxrange : x ∈ LinearMap.range ((mulP p k).rTensor M) := by
    rw [← LinearMap.exact_iff.mp hexact]
    exact hxker
  obtain ⟨z, hz⟩ := hxrange
  refine ⟨TensorProduct.lid (W₂ p k) M z, ?_⟩
  have hz' := congrArg (TensorProduct.lid (W₂ p k) M) hz
  rw [lid_rTensor_mulP p k z] at hz'
  have hx_lid : TensorProduct.lid (W₂ p k) M x = m := by
    exact (TensorProduct.lid (W₂ p k) M).apply_symm_apply m
  rw [hx_lid] at hz'
  exact hz'.symm

/-- Multiplication by `p` remains exact after tensoring with a flat module. -/
lemma exists_eq_p_smul_of_p_smul_eq_zero [PerfectField k]
    [Module.Flat (W₂ p k) M] (m : M)
    (hm : (p : W₂ p k) • m = 0) :
    ∃ m' : M, m = (p : W₂ p k) • m' := by
  let x : W₂ p k ⊗[W₂ p k] M :=
    (TensorProduct.lid (W₂ p k) M).symm m
  have hx : (mulP p k).rTensor M x = 0 := by
    apply (TensorProduct.lid (W₂ p k) M).injective
    rw [lid_rTensor_mulP p k x,
      (TensorProduct.lid (W₂ p k) M).apply_symm_apply, hm, map_zero]
  have hexact : Exact ((mulP p k).rTensor M) ((mulP p k).rTensor M) :=
    Module.Flat.rTensor_exact M (exact_mulP_mulP p k)
  have hxker : x ∈ LinearMap.ker ((mulP p k).rTensor M) := hx
  have hxrange : x ∈ LinearMap.range ((mulP p k).rTensor M) := by
    rw [← LinearMap.exact_iff.mp hexact]
    exact hxker
  obtain ⟨z, hz⟩ := hxrange
  refine ⟨TensorProduct.lid (W₂ p k) M z, ?_⟩
  have hz' := congrArg (TensorProduct.lid (W₂ p k) M) hz
  rw [lid_rTensor_mulP p k z] at hz'
  have hx_lid : TensorProduct.lid (W₂ p k) M x = m :=
    (TensorProduct.lid (W₂ p k) M).apply_symm_apply m
  rw [hx_lid] at hz'
  exact hz'.symm

/-- A `p`-multiple has zero image on the special fibre. -/
lemma toSpecialFiber_p_smul (m : M) :
    toSpecialFiber p k ((p : W₂ p k) • m) = 0 := by
  rw [toSpecialFiber_apply, TensorProduct.tmul_smul]
  change (w₂Reduction p k (p : W₂ p k) • (1 : k)) ⊗ₜ[W₂ p k] m = 0
  rw [map_natCast, CharP.cast_eq_zero, zero_smul,
    TensorProduct.zero_tmul]

/-- Division by `p`, followed by reduction, is unique on a flat module. -/
lemma toSpecialFiber_eq_of_p_smul_eq [PerfectField k]
    [Module.Flat (W₂ p k) M] {x y : M}
    (h : (p : W₂ p k) • x = (p : W₂ p k) • y) :
    toSpecialFiber p k x = toSpecialFiber p k y := by
  have hzero : (p : W₂ p k) • (x - y) = 0 := by
    rw [smul_sub, h, sub_self]
  obtain ⟨z, hz⟩ :=
    exists_eq_p_smul_of_p_smul_eq_zero p k (x - y) hzero
  apply sub_eq_zero.mp
  rw [← map_sub, hz, toSpecialFiber_p_smul]

/-- A noncomputable representative of division by `p`.  Its special-fibre
image is independent of this representative by
`toSpecialFiber_eq_of_p_smul_eq`. -/
private noncomputable def divideChoice [PerfectField k]
    [Module.Flat (W₂ p k) M]
    (x : LinearMap.ker (toSpecialFiber (M := M) p k)) : M :=
  (exists_eq_p_smul_of_toSpecialFiber_eq_zero p k x.1 x.2).choose

private lemma divideChoice_spec [PerfectField k]
    [Module.Flat (W₂ p k) M]
    (x : LinearMap.ker (toSpecialFiber (M := M) p k)) :
    x.1 = (p : W₂ p k) • divideChoice p k x :=
  (exists_eq_p_smul_of_toSpecialFiber_eq_zero p k x.1 x.2).choose_spec

/-- Canonical division by `p` modulo `p`: an element vanishing on the
special fibre is divided by `p`, and the quotient is then reduced. -/
noncomputable def divideByP [PerfectField k]
    [Module.Flat (W₂ p k) M] :
    LinearMap.ker (toSpecialFiber (M := M) p k) →ₗ[W₂ p k]
      k ⊗[W₂ p k] M where
  toFun x := toSpecialFiber p k (divideChoice p k x)
  map_add' x y := by
    rw [← map_add]
    apply toSpecialFiber_eq_of_p_smul_eq p k
    calc
      (p : W₂ p k) • divideChoice p k (x + y) = (x + y).1 :=
        (divideChoice_spec p k (x + y)).symm
      _ = x.1 + y.1 := rfl
      _ = (p : W₂ p k) • divideChoice p k x +
          (p : W₂ p k) • divideChoice p k y := by
        rw [divideChoice_spec p k x, divideChoice_spec p k y]
      _ = (p : W₂ p k) •
          (divideChoice p k x + divideChoice p k y) := (smul_add _ _ _).symm
  map_smul' a x := by
    rw [← map_smul]
    apply toSpecialFiber_eq_of_p_smul_eq p k
    calc
      (p : W₂ p k) • divideChoice p k (a • x) = (a • x).1 :=
        (divideChoice_spec p k (a • x)).symm
      _ = a • x.1 := rfl
      _ = a • ((p : W₂ p k) • divideChoice p k x) := by
        rw [← divideChoice_spec p k x]
      _ = (p : W₂ p k) • (a • divideChoice p k x) := by
        rw [smul_comm]

/-- Characterizing formula for `divideByP`, independent of the internal
choice of a quotient. -/
lemma divideByP_eq_of_eq_p_smul [PerfectField k]
    [Module.Flat (W₂ p k) M]
    (x : LinearMap.ker (toSpecialFiber (M := M) p k)) (m : M)
    (h : x.1 = (p : W₂ p k) • m) :
    divideByP p k x = toSpecialFiber p k m := by
  apply toSpecialFiber_eq_of_p_smul_eq p k
  rw [← divideChoice_spec p k x, h]

end WittLengthTwo

end

end LSZ
