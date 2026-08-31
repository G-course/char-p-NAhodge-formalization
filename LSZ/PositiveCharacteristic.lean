import LSZ.GeometricObjects
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Restricted powers in positive characteristic

This file is the first layer which assumes positive characteristic.  The
ordinary Higgs and connection categories do not import it.
-/

open Finset Nat

namespace Derivation

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The generalized Leibniz formula for an iterated ring derivation. -/
theorem iterate_apply_mul (D : Derivation R A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) =
      ∑ ij ∈ antidiagonal n, choose n ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (M := A) (fun i j => D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul,
      leibniz, smul_eq_mul, smul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm, mul_comm]

/-- Range-indexed form of the generalized Leibniz formula. -/
theorem iterate_apply_mul' (D : Derivation R A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) =
      ∑ i ∈ range (n + 1), choose n i • (D^[i] a * D^[n - i] b) := by
  rw [iterate_apply_mul D n a b]
  exact sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • (D^[i] a * D^[j] b)) n

/-- In characteristic `p`, for prime `p`, the `p`-fold iterate of a
derivation satisfies the Leibniz rule. -/
theorem iterate_prime_leibniz (D : Derivation R A A) (p : ℕ)
    [CharP A p] (hp : p.Prime) (a b : A) :
    D^[p] (a * b) = a * D^[p] b + b * D^[p] a := by
  let f : ℕ → A := fun i => choose p i • (D^[i] a * D^[p - i] b)
  have hsubset : ({0, p} : Finset ℕ) ⊆ range (p + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hoff : ∀ i ∈ range (p + 1), i ∉ ({0, p} : Finset ℕ) → f i = 0 := by
    intro i hiRange hiEndpoints
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      simp at hiEndpoints
    have hip : i ≠ p := by
      intro hi
      subst i
      simp at hiEndpoints
    have hip' : i < p := by
      simp only [mem_range] at hiRange
      omega
    have hcast : (choose p i : A) = 0 :=
      (CharP.cast_eq_zero_iff A p (choose p i)).2 (hp.dvd_choose_self hi0 hip')
    simp [f, nsmul_eq_mul, hcast]
  calc
    D^[p] (a * b) = ∑ i ∈ range (p + 1), f i := by
      simpa [f] using iterate_apply_mul' D p a b
    _ = ∑ i ∈ ({0, p} : Finset ℕ), f i :=
      (sum_subset hsubset hoff).symm
    _ = a * D^[p] b + b * D^[p] a := by
      rw [sum_insert (by simpa using hp.ne_zero.symm), sum_singleton]
      simp [f, mul_comm]

/-- The restricted `p`-power of a derivation when the target ring itself is
known to have characteristic `p`. -/
def restrictedPower (D : Derivation R A A) (p : ℕ)
    [CharP A p] [hp : Fact p.Prime] : Derivation R A A :=
  Derivation.mk' (D.toLinearMap ^ p) (fun a b => by
    simp only [Module.End.pow_apply, smul_eq_mul]
    exact iterate_prime_leibniz D p hp.out a b)

@[simp]
theorem restrictedPower_apply (D : Derivation R A A) (p : ℕ)
    [CharP A p] [Fact p.Prime] (a : A) :
    restrictedPower D p a = D^[p] a := by
  apply Module.End.pow_apply

end Derivation

namespace Derivation

universe u v

variable {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]

/-- The restricted `p`-power over a field, including the zero-ring case.

For a nontrivial `K`-algebra, the algebra map is injective and transfers
characteristic `p` from `K` to `B`.  If `B` is the zero ring, both sides of
the defining evaluation equality are automatically equal. -/
noncomputable def restrictedPowerField (D : Derivation K B B) (p : ℕ)
    [CharP K p] [Fact p.Prime] : Derivation K B B := by
  classical
  by_cases h : Nontrivial B
  · letI : Nontrivial B := h
    letI : CharP B p :=
      charP_of_injective_algebraMap (algebraMap K B).injective p
    exact restrictedPower D p
  · exact 0

@[simp]
theorem restrictedPowerField_apply (D : Derivation K B B) (p : ℕ)
    [CharP K p] [Fact p.Prime] (b : B) :
    restrictedPowerField D p b = D^[p] b := by
  classical
  by_cases h : Nontrivial B
  · letI : Nontrivial B := h
    letI : CharP B p :=
      charP_of_injective_algebraMap (algebraMap K B).injective p
    simp [restrictedPowerField, h]
  · rw [restrictedPowerField]
    simp only [h, ↓reduceDIte, Derivation.zero_apply]
    haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

end Derivation

namespace LSZ

universe u v

/-- A map intertwining two endomorphisms also intertwines all their
iterates. -/
lemma map_iterate {A : Type u} {B : Type v} (r : A → B) (f : A → A) (g : B → B)
    (h : ∀ x, r (f x) = g (r x)) (n : ℕ) (x : A) :
    r (f^[n] x) = g^[n] (r x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

namespace SmoothScheme.VectorField

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

variable {k : Type u} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} {U V : X.scheme.Opens}

local instance characteristicPrime : Fact (ringChar k).Prime :=
  CharP.char_is_prime_of_pos k (ringChar k)

/-- The canonical restricted power of a relative vector field. -/
noncomputable def pPower (D : X.VectorField U) : X.VectorField U where
  deriv V hV := Derivation.restrictedPowerField (D.deriv V hV) (ringChar k)
  compatible hV hWV a := by
    simp only [Derivation.restrictedPowerField_apply]
    exact map_iterate
      (X.scheme.presheaf.map (homOfLE hWV).op)
      (D.deriv _ hV) (D.deriv _ (hWV.trans hV))
      (D.compatible hV hWV) (ringChar k) a

@[simp]
lemma pPower_deriv (D : X.VectorField U) (V : X.scheme.Opens) (hV : V ≤ U) :
    D.pPower.deriv V hV =
      Derivation.restrictedPowerField (D.deriv V hV) (ringChar k) := rfl

@[simp]
lemma pPower_act (D : X.VectorField U) (a : Γ(X.scheme, U)) :
    D.pPower.act a = D.act^[ringChar k] a :=
  Derivation.restrictedPowerField_apply _ _ _

@[simp]
lemma pPower_restrict (D : X.VectorField U) (hVU : V ≤ U) :
    D.pPower.restrict hVU = (D.restrict hVU).pPower := by
  ext W hW a
  rfl

end SmoothScheme.VectorField

end LSZ
