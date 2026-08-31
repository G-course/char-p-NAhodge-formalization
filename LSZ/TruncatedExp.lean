import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-!
# The characteristic-`p` truncated exponential

For `p` prime and an algebra in characteristic `p`, the coefficients
`1 / i!` exist for `i < p`.  The LSZ transition function is the finite sum

`  exp_p(a) = ∑_{0 ≤ i < p} a^i / i! .`

The addition theorem below uses the exact LSZ hypothesis: every mixed word
of total length at least `p` vanishes.  Merely assuming `a^p = b^p = 0`
would not suffice for the truncated addition formula.
-/

open Finset
open scoped BigOperators

namespace LSZ

namespace TruncatedExp

variable (p : ℕ) {A : Type*}
variable [Ring A] [Fact p.Prime] [Algebra (ZMod p) A]

/-- The LSZ truncated exponential in characteristic `p`. -/
noncomputable def exp (a : A) : A :=
  ∑ i ∈ range p, ((i.factorial : ZMod p)⁻¹) • a ^ i

@[simp]
lemma exp_zero : exp p (0 : A) = 1 := by
  have hp : p.Prime := Fact.out
  rw [exp, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    simp [hi0]
  · simp [hp.pos]

@[simp]
lemma exp_neg_zero : exp p (-(0 : A)) = 1 := by
  simp

/-- The factorial coefficient identity used in the binomial calculation. -/
private lemma invFactorial_mul_choose {n i : ℕ} (hn : n < p) (hi : i ≤ n) :
    ((n.factorial : ZMod p)⁻¹) * (n.choose i : ZMod p) =
      ((i.factorial : ZMod p)⁻¹) * (((n - i).factorial : ZMod p)⁻¹) := by
  have hnUnit : IsUnit (n.factorial : ZMod p) :=
    (IsUnit.natCast_factorial_iff_of_charP p).2 hn
  have hiUnit : IsUnit (i.factorial : ZMod p) :=
    hnUnit.natCast_factorial_of_le hi
  have hniUnit : IsUnit ((n - i).factorial : ZMod p) :=
    hnUnit.natCast_factorial_of_le (Nat.sub_le n i)
  have hchoose :
      (n.choose i : ZMod p) =
        (n.factorial : ZMod p) * (i.factorial : ZMod p)⁻¹ *
          ((n - i).factorial : ZMod p)⁻¹ := by
    simpa [Finset.mem_antidiagonal] using
      (Nat.castChoose_eq hnUnit
        (show (i, n - i) ∈ Finset.antidiagonal n by
          rw [Finset.mem_antidiagonal]
          exact Nat.add_sub_of_le hi))
  rw [hchoose]
  simp only [← mul_assoc, inv_mul_cancel₀ hnUnit.ne_zero, one_mul]

/-- The truncated exponential turns addition into multiplication when the
two elements commute and all mixed monomials of total degree at least `p`
vanish. -/
theorem exp_add_of_commute_of_jointNilpotent {a b : A}
    (hcomm : Commute a b)
    (hzero : ∀ i j : ℕ, p ≤ i + j → a ^ i * b ^ j = 0) :
    exp p (a + b) = exp p a * exp p b := by
  let Rp := range p
  have hleft :
      exp p (a + b) =
        ∑ ij ∈ Rp ×ˢ Rp with ij.1 + ij.2 < p,
          (((ij.1.factorial : ZMod p)⁻¹) *
              ((ij.2.factorial : ZMod p)⁻¹)) •
            (a ^ ij.1 * b ^ ij.2) := by
    calc
      exp p (a + b) =
          ∑ n ∈ Rp, ((n.factorial : ZMod p)⁻¹) • (a + b) ^ n := rfl
      _ = ∑ n ∈ Rp, ∑ i ∈ range (n + 1),
          ((((i.factorial : ZMod p)⁻¹) *
              (((n - i).factorial : ZMod p)⁻¹)) •
            (a ^ i * b ^ (n - i))) := by
        apply sum_congr rfl
        intro n hn
        rw [hcomm.add_pow]
        simp_rw [smul_sum]
        apply sum_congr rfl
        intro i hi
        have hnp : n < p := by simpa [Rp] using hn
        have hin : i ≤ n := Nat.le_of_lt_succ (by simpa using hi)
        have hcoeff := invFactorial_mul_choose (p := p) hnp hin
        rw [← Nat.cast_commute (n.choose i), ← hcoeff,
          ← mul_smul_comm, ← nsmul_eq_mul, mul_smul,
          ← smul_assoc, smul_comm, smul_assoc]
        norm_cast
      _ = ∑ ij ∈ Rp ×ˢ Rp with ij.1 + ij.2 < p,
          (((ij.1.factorial : ZMod p)⁻¹) *
              ((ij.2.factorial : ZMod p)⁻¹)) •
            (a ^ ij.1 * b ^ ij.2) := by
        rw [show Rp = range p from rfl, sum_sigma']
        apply sum_bij (fun ⟨n, i⟩ _ ↦ (i, n - i))
        · simp only [mem_sigma, mem_range, mem_filter, mem_product, and_imp]
          omega
        · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
          rintro ⟨n₁, i₁⟩ - hn₁ ⟨n₂, i₂⟩ - hn₂ h₁ h₂
          simp_all
          omega
        · simp only [mem_filter, mem_product, mem_range, mem_sigma,
            exists_prop, Sigma.exists, and_imp, Prod.forall, Prod.mk.injEq]
          intro i j hi hj hij
          exact ⟨i + j, i, by omega⟩
        · simp only [mem_sigma, mem_range, implies_true]
  have hhigh :
      ∑ ij ∈ Rp ×ˢ Rp with ¬ ij.1 + ij.2 < p,
          (((ij.1.factorial : ZMod p)⁻¹) *
              ((ij.2.factorial : ZMod p)⁻¹)) •
            (a ^ ij.1 * b ^ ij.2) = 0 := by
    apply sum_eq_zero
    intro ij hij
    rw [mem_filter] at hij
    rw [hzero ij.1 ij.2 (Nat.le_of_not_gt hij.2), smul_zero]
  have hsplit := sum_filter_add_sum_filter_not (Rp ×ˢ Rp)
    (fun ij ↦ ij.1 + ij.2 < p)
    (fun ij ↦ (((ij.1.factorial : ZMod p)⁻¹) *
        ((ij.2.factorial : ZMod p)⁻¹)) • (a ^ ij.1 * b ^ ij.2))
  rw [hhigh, add_zero] at hsplit
  have hproduct :
      exp p a * exp p b =
        ∑ ij ∈ Rp ×ˢ Rp,
          (((ij.1.factorial : ZMod p)⁻¹) *
              ((ij.2.factorial : ZMod p)⁻¹)) •
            (a ^ ij.1 * b ^ ij.2) := by
    calc
      exp p a * exp p b =
          ∑ i ∈ Rp, ∑ j ∈ Rp,
            (((i.factorial : ZMod p)⁻¹) *
                ((j.factorial : ZMod p)⁻¹)) •
              (a ^ i * b ^ j) := by
        rw [exp, exp, sum_mul_sum]
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ∑ ij ∈ Rp ×ˢ Rp,
          (((ij.1.factorial : ZMod p)⁻¹) *
              ((ij.2.factorial : ZMod p)⁻¹)) •
            (a ^ ij.1 * b ^ ij.2) := by
        rw [sum_sigma']
        apply sum_bijective (fun ⟨i, j⟩ ↦ (i, j))
        · exact ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h ↦ by cases h; rfl,
            fun ⟨i, j⟩ ↦ ⟨⟨i, j⟩, rfl⟩⟩
        · simp only [mem_sigma, mem_product, implies_true]
        · simp only [implies_true]
  rw [hleft, hsplit]
  exact hproduct.symm

/-- A convenient consequence: the inverse candidate is the exponential of
the negative whenever the corresponding mixed words vanish. -/
theorem exp_mul_exp_neg_eq_one {a : A}
    (hzero : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0) :
    exp p a * exp p (-a) = 1 := by
  rw [← exp_add_of_commute_of_jointNilpotent p (Commute.neg_right rfl) hzero]
  simp

/-- The other inverse identity. -/
theorem exp_neg_mul_exp_eq_one {a : A}
    (hzero : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) :
    exp p (-a) * exp p a = 1 := by
  rw [← exp_add_of_commute_of_jointNilpotent p (Commute.neg_left rfl) hzero]
  simp

/-- The truncated exponential as a unit, with the two LSZ nilpotence
identities made explicit. -/
noncomputable def unit (a : A)
    (h₁ : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0)
    (h₂ : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) : Aˣ where
  val := exp p a
  inv := exp p (-a)
  val_inv := exp_mul_exp_neg_eq_one p h₁
  inv_val := exp_neg_mul_exp_eq_one p h₂

@[simp]
lemma coe_unit (a : A)
    (h₁ : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0)
    (h₂ : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) :
    ↑(unit p a h₁ h₂) = exp p a := rfl

section ModuleEnd

variable {R M : Type*} [CommRing R] [CharP R p]
variable [AddCommGroup M] [Module R M]

/-- The truncated exponential of an `R`-linear endomorphism when `R` has
characteristic `p`.  This wrapper installs the canonical `ZMod p`-algebra
structure, so later LSZ transition maps do not have to repeat typeclass
plumbing on every open set. -/
noncomputable def moduleEndExp (a : Module.End R M) : Module.End R M := by
  letI : Algebra (ZMod p) R := ZMod.algebra R p
  letI : Module (ZMod p) M := Module.compHom M (algebraMap (ZMod p) R)
  letI : IsScalarTower (ZMod p) R M := IsScalarTower.of_compHom (ZMod p) R M
  letI : SMulCommClass R (ZMod p) M :=
    ⟨fun r z m => by
      change r • ((algebraMap (ZMod p) R z) • m) =
        (algebraMap (ZMod p) R z) • (r • m)
      simp only [smul_smul, mul_comm]⟩
  exact exp p a

theorem moduleEndExp_add_of_commute_of_jointNilpotent {a b : Module.End R M}
    (hcomm : Commute a b)
    (hzero : ∀ i j : ℕ, p ≤ i + j → a ^ i * b ^ j = 0) :
    moduleEndExp p (a + b) = moduleEndExp p a * moduleEndExp p b := by
  letI : Algebra (ZMod p) R := ZMod.algebra R p
  letI : Module (ZMod p) M := Module.compHom M (algebraMap (ZMod p) R)
  letI : IsScalarTower (ZMod p) R M := IsScalarTower.of_compHom (ZMod p) R M
  letI : SMulCommClass R (ZMod p) M :=
    ⟨fun r z m => by
      change r • ((algebraMap (ZMod p) R z) • m) =
        (algebraMap (ZMod p) R z) • (r • m)
      simp only [smul_smul, mul_comm]⟩
  exact exp_add_of_commute_of_jointNilpotent p hcomm hzero

theorem moduleEndExp_mul_neg_eq_one {a : Module.End R M}
    (hzero : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0) :
    moduleEndExp p a * moduleEndExp p (-a) = 1 := by
  letI : Algebra (ZMod p) R := ZMod.algebra R p
  letI : Module (ZMod p) M := Module.compHom M (algebraMap (ZMod p) R)
  letI : IsScalarTower (ZMod p) R M := IsScalarTower.of_compHom (ZMod p) R M
  letI : SMulCommClass R (ZMod p) M :=
    ⟨fun r z m => by
      change r • ((algebraMap (ZMod p) R z) • m) =
        (algebraMap (ZMod p) R z) • (r • m)
      simp only [smul_smul, mul_comm]⟩
  exact exp_mul_exp_neg_eq_one p hzero

theorem moduleEndExp_neg_mul_eq_one {a : Module.End R M}
    (hzero : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) :
    moduleEndExp p (-a) * moduleEndExp p a = 1 := by
  letI : Algebra (ZMod p) R := ZMod.algebra R p
  letI : Module (ZMod p) M := Module.compHom M (algebraMap (ZMod p) R)
  letI : IsScalarTower (ZMod p) R M := IsScalarTower.of_compHom (ZMod p) R M
  letI : SMulCommClass R (ZMod p) M :=
    ⟨fun r z m => by
      change r • ((algebraMap (ZMod p) R z) • m) =
        (algebraMap (ZMod p) R z) • (r • m)
      simp only [smul_smul, mul_comm]⟩
  exact exp_neg_mul_exp_eq_one p hzero

/-- The LSZ exponential gauge as an honest linear automorphism. -/
noncomputable def moduleEndLinearEquiv (a : Module.End R M)
    (h₁ : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0)
    (h₂ : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) : M ≃ₗ[R] M :=
  LinearEquiv.ofLinear (moduleEndExp p a) (moduleEndExp p (-a))
    (by
      change moduleEndExp p a * moduleEndExp p (-a) = 1
      exact moduleEndExp_mul_neg_eq_one p h₁)
    (by
      change moduleEndExp p (-a) * moduleEndExp p a = 1
      exact moduleEndExp_neg_mul_eq_one p h₂)

@[simp]
lemma moduleEndLinearEquiv_apply (a : Module.End R M)
    (h₁ : ∀ i j : ℕ, p ≤ i + j → a ^ i * (-a) ^ j = 0)
    (h₂ : ∀ i j : ℕ, p ≤ i + j → (-a) ^ i * a ^ j = 0) (m : M) :
    moduleEndLinearEquiv p a h₁ h₂ m = moduleEndExp p a m := rfl

end ModuleEnd

/-- Explicit-instance wrapper for section rings.  A
`RestrictedTangentSheaf` stores `CharP Γ(U) p` as data rather than as a
global typeclass, so LSZ gauge formulas use this version. -/
noncomputable def moduleEndExpOf {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (hR : CharP R p)
    (a : Module.End R M) : Module.End R M := by
  letI : CharP R p := hR
  exact moduleEndExp p a

end TruncatedExp

end LSZ
