import LSZ.PCurvature
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Jacobson and Hochschild identities for p-curvature

This file proves the noncommutative Jacobson formula and Hochschild's
scalar formula from first principles, then applies them to restricted
powers of vector fields and to the Frobenius semilinearity of p-curvature.
-/

open Finset
open scoped Polynomial

namespace LSZ

theorem signed_choose_pred_cast {K : Type*} [Field K]
    (p : ℕ) [CharP K p] (hp : p.Prime) (j : ℕ) (hj : j < p) :
    ((-1 : K) ^ j) * (Nat.choose (p - 1) j : K) = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjp : j < p := j.lt_succ_self.trans hj
      have hjle : j ≤ p - 1 := Nat.le_sub_one_of_lt hjp
      have hnat := Nat.choose_succ_right_eq (p - 1) j
      have hcast :
          (Nat.choose (p - 1) (j + 1) : K) * (j + 1 : ℕ) =
            (Nat.choose (p - 1) j : K) * ((p - 1) - j : ℕ) := by
        simpa only [Nat.cast_mul] using
          congrArg (fun n : ℕ => (n : K)) hnat
      have hsub : (((p - 1) - j : ℕ) : K) = -((j + 1 : ℕ) : K) := by
        rw [Nat.cast_sub hjle]
        have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
        rw [Nat.cast_sub hp.one_le, Nat.cast_one, hp0]
        push_cast
        ring
      have hj1ne : (((j + 1 : ℕ) : K)) ≠ 0 := by
        intro hzero
        have hdvd : p ∣ j + 1 :=
          (CharP.cast_eq_zero_iff K p (j + 1)).1 hzero
        have hle : p ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) hdvd
        omega
      have hchoose :
          (Nat.choose (p - 1) (j + 1) : K) =
            -(Nat.choose (p - 1) j : K) := by
        apply mul_right_cancel₀ hj1ne
        rw [hcast, hsub]
        ring
      rw [pow_succ, hchoose]
      calc
        (-1 : K) ^ j * -1 * -(Nat.choose (p - 1) j : K) =
            (-1 : K) ^ j * (Nat.choose (p - 1) j : K) := by ring
        _ = 1 := ih hjp

def jacobsonCoeff {L : Type*} [Zero L] [Add L] [Bracket L L]
    (x y : L) : ℕ → ℕ → L
  | 0, 0 => x
  | 0, _ + 1 => 0
  | n + 1, 0 => ⁅y, jacobsonCoeff x y n 0⁆
  | n + 1, i + 1 =>
      ⁅y, jacobsonCoeff x y n (i + 1)⁆ +
        ⁅x, jacobsonCoeff x y n i⁆

/-- The universal correction term in Jacobson's formula. -/
noncomputable def jacobsonCorrection (K : Type*) {L : Type*}
    [Field K] [AddCommGroup L] [Module K L] [Bracket L L]
    (p : ℕ) (x y : L) : L :=
  ∑ j ∈ range (p - 1),
    (((j + 1 : ℕ) : K)⁻¹) • jacobsonCoeff x y (p - 1) j

section LinearMap

variable {K L M : Type*} [Field K]
variable [AddCommGroup L] [Module K L] [Bracket L L]
variable [AddCommGroup M] [Module K M] [Bracket M M]

theorem jacobsonCoeff_map_linear (f : L →ₗ[K] M)
    (hbracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (x y : L) (n i : ℕ) :
    f (jacobsonCoeff x y n i) = jacobsonCoeff (f x) (f y) n i := by
  induction n generalizing i with
  | zero =>
      cases i <;> simp [jacobsonCoeff]
  | succ n ih =>
      cases i with
      | zero => simp [jacobsonCoeff, ih, hbracket]
      | succ i => simp [jacobsonCoeff, ih, hbracket]

theorem jacobsonCorrection_map_linear (f : L →ₗ[K] M)
    (hbracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (p : ℕ) (x y : L) :
    f (jacobsonCorrection K p x y) =
      jacobsonCorrection K p (f x) (f y) := by
  simp [jacobsonCorrection, jacobsonCoeff_map_linear f hbracket]

end LinearMap

section Map

variable {K L M : Type*} [Field K]
variable [LieRing L] [LieAlgebra K L]
variable [LieRing M] [LieAlgebra K M]

theorem jacobsonCoeff_map (f : L →ₗ⁅K⁆ M) (x y : L) (n i : ℕ) :
    f (jacobsonCoeff x y n i) = jacobsonCoeff (f x) (f y) n i := by
  exact jacobsonCoeff_map_linear f.toLinearMap f.map_lie x y n i

theorem jacobsonCorrection_map (f : L →ₗ⁅K⁆ M)
    (p : ℕ) (x y : L) :
    f (jacobsonCorrection K p x y) =
      jacobsonCorrection K p (f x) (f y) := by
  exact jacobsonCorrection_map_linear f.toLinearMap f.map_lie p x y

end Map

section

variable {B : Type*} [Ring B]

noncomputable def adPolynomial (x y : B) : ℕ → B[X]
  | 0 => Polynomial.C x
  | n + 1 =>
      let z := Polynomial.X * Polynomial.C x + Polynomial.C y
      z * adPolynomial x y n - adPolynomial x y n * z

theorem coeff_adPolynomial (x y : B) (n i : ℕ) :
    (adPolynomial x y n).coeff i = jacobsonCoeff x y n i := by
  induction n generalizing i with
  | zero =>
      cases i <;> simp [adPolynomial, jacobsonCoeff]
  | succ n ih =>
      cases i with
      | zero =>
          simp [adPolynomial, jacobsonCoeff, ih, Ring.lie_def]
      | succ i =>
          have hright :
              (adPolynomial x y n * (Polynomial.C x * Polynomial.X)).coeff (i + 1) =
                jacobsonCoeff x y n i * x := by
            rw [← mul_assoc, Polynomial.coeff_mul_X,
              Polynomial.coeff_mul_C, ih]
          simp [adPolynomial, jacobsonCoeff, ih, add_mul, mul_add,
            add_assoc, sub_eq_add_neg, Ring.lie_def, hright,
            mul_assoc]
          abel

/-- Leibniz's formula for the derivative of a power, without assuming that
the coefficient ring is commutative. -/
theorem derivative_pow_noncomm (q : B[X]) (n : ℕ) :
    Polynomial.derivative (q ^ n) =
      ∑ i ∈ range n,
        q ^ i * Polynomial.derivative q * q ^ (n - 1 - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.derivative_mul, ih, sum_mul,
        sum_range_succ]
      congr 1
      · refine sum_congr rfl fun i hi ↦ ?_
        simp only [mem_range] at hi
        have hpow : n - 1 - i + 1 = n - i := by omega
        simp only [Nat.add_sub_cancel]
        rw [mul_assoc (q ^ i * Polynomial.derivative q),
          ← pow_succ, hpow]
      · simp

end

section

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

local instance : LieRing B := LieRing.ofAssociativeRing

theorem ad_pow_pred_eq_sum (p : ℕ) [CharP K p] (hp : p.Prime)
    (z w : B) :
    (LieAlgebra.ad K B z ^ (p - 1)) w =
      ∑ ij ∈ antidiagonal (p - 1), z ^ ij.1 * w * z ^ ij.2 := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  change ((LinearMap.mulLeft K z - LinearMap.mulRight K z) ^ (p - 1)) w = _
  rw [sub_eq_add_neg,
    ((LinearMap.commute_mulLeft_right z z).neg_right.add_pow' (p - 1))]
  simp only [LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply,
    LinearMap.pow_mulLeft,
    LinearMap.pow_mulRight, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply]
  have hnegpow : ∀ (n : ℕ) (b : B),
      ((-LinearMap.mulRight K z) ^ n) b =
        (-1 : K) ^ n • (b * z ^ n) := by
    intro n b
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply,
          LinearMap.mulRight_apply, ih, pow_succ]
        simp only [smul_mul_assoc, pow_succ, mul_neg, mul_one,
          neg_smul, mul_assoc]
  refine sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
  dsimp only [Prod.fst, Prod.snd] at *
  change Nat.choose (p - 1) i •
      ((LinearMap.mulLeft K (z ^ i) *
        (-LinearMap.mulRight K z) ^ j) w) = z ^ i * w * z ^ j
  have hij' : i + j = p - 1 := mem_antidiagonal.1 hij
  have hjp : j < p := by
    have hp2 := hp.two_le
    omega
  have hsigned := signed_choose_pred_cast (K := K) p hp j hjp
  rw [Nat.choose_symm_of_eq_add hij'.symm]
  rw [Module.End.mul_apply, hnegpow, LinearMap.mulLeft_apply]
  rw [← Nat.cast_smul_eq_nsmul K, mul_smul_comm, smul_smul,
    mul_comm, hsigned, one_smul]
  rw [mul_assoc]

/-- The polynomial encoding the iterated adjoint is the derivative of the
`p`-th power of the generic affine line `t x + y`. -/
theorem adPolynomial_pred_eq_derivative_pow (p : ℕ) [CharP K p]
    (hp : p.Prime) (x y : B) :
    adPolynomial x y (p - 1) =
      Polynomial.derivative
        ((Polynomial.X * Polynomial.C x + Polynomial.C y) ^ p) := by
  let z : B[X] := Polynomial.X * Polynomial.C x + Polynomial.C y
  letI : LieRing B[X] := LieRing.ofAssociativeRing
  have had : ∀ n : ℕ,
      adPolynomial x y n =
        (LieAlgebra.ad K B[X] z ^ n) (Polynomial.C x) := by
    intro n
    induction n with
    | zero => simp [adPolynomial]
    | succ n ih =>
        rw [adPolynomial, pow_succ', Module.End.mul_apply, ← ih]
        rfl
  rw [had, ad_pow_pred_eq_sum p hp]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [derivative_pow_noncomm]
  simp only [z, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, mul_zero, add_zero, one_mul]
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le]

private theorem natCast_succ_ne_zero (p : ℕ) [CharP K p]
    (hp : p.Prime) (j : ℕ) (hj : j < p - 1) :
    (((j + 1 : ℕ) : K)) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ j + 1 :=
    (CharP.cast_eq_zero_iff K p (j + 1)).1 hzero
  have hle : p ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) hdvd
  omega

/-- Every middle coefficient in the generic noncommutative binomial is the
corresponding Jacobson coefficient divided by its degree. -/
theorem coeff_generic_pow_eq_jacobson (p : ℕ) [CharP K p]
    (hp : p.Prime) (x y : B) (j : ℕ) (hj : j < p - 1) :
    ((Polynomial.X * Polynomial.C x + Polynomial.C y) ^ p).coeff (j + 1) =
      (((j + 1 : ℕ) : K)⁻¹) • jacobsonCoeff x y (p - 1) j := by
  let z : B[X] := Polynomial.X * Polynomial.C x + Polynomial.C y
  have hcoeff := congrArg (fun q : B[X] => q.coeff j)
    (adPolynomial_pred_eq_derivative_pow (K := K) p hp x y)
  rw [coeff_adPolynomial, Polynomial.coeff_derivative] at hcoeff
  change jacobsonCoeff x y (p - 1) j =
    (z ^ p).coeff (j + 1) * ((j : B) + 1) at hcoeff
  have hscalar :
      (z ^ p).coeff (j + 1) * ((j : B) + 1) =
        ((j : K) + 1) • (z ^ p).coeff (j + 1) := by
    simpa [Nat.cast_add, Algebra.smul_def] using
      (Nat.cast_commute (j + 1) ((z ^ p).coeff (j + 1))).eq.symm
  rw [hscalar] at hcoeff
  have hne : (j : K) + 1 ≠ 0 := by
    simpa [Nat.cast_add] using natCast_succ_ne_zero (K := K) p hp j hj
  have hzresult :
      (z ^ p).coeff (j + 1) =
        ((j : K) + 1)⁻¹ • jacobsonCoeff x y (p - 1) j := by
    calc
      (z ^ p).coeff (j + 1) =
          (1 : K) • (z ^ p).coeff (j + 1) := by simp
      _ = (((j : K) + 1)⁻¹ * ((j : K) + 1)) •
            (z ^ p).coeff (j + 1) := by rw [inv_mul_cancel₀ hne]
      _ = ((j : K) + 1)⁻¹ •
            (((j : K) + 1) • (z ^ p).coeff (j + 1)) := by
              rw [smul_smul]
      _ = ((j : K) + 1)⁻¹ • jacobsonCoeff x y (p - 1) j := by
            rw [← hcoeff]
  simpa [z, Nat.cast_add] using hzresult

/-- Jacobson's formula in an associative algebra of prime characteristic. -/
theorem add_pow_eq_add_pow_add_jacobson (p : ℕ) [CharP K p]
    (hp : p.Prime) (x y : B) :
    (x + y) ^ p = x ^ p + y ^ p + jacobsonCorrection K p x y := by
  let z : B[X] := Polynomial.X * Polynomial.C x + Polynomial.C y
  have hz : z.natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    apply max_le
    · exact (Polynomial.natDegree_mul_C_le Polynomial.X x).trans
        Polynomial.natDegree_X_le
    · simpa using Polynomial.natDegree_C_le y
  have hzp : (z ^ p).natDegree ≤ p := by
    simpa using Polynomial.natDegree_pow_le_of_le p hz
  let ev1 : B[X] →+* B :=
    Polynomial.eval₂RingHom' (RingHom.id B) 1 (fun _ => Commute.one_right _)
  have heval : ev1 (z ^ p) = (x + y) ^ p := by
    rw [map_pow]
    congr 1
    simp [ev1, z]
  have hsum := Polynomial.eval₂_eq_sum_range'
    (RingHom.id B) (Nat.lt_succ_of_le hzp) (1 : B)
  change ev1 (z ^ p) = _ at hsum
  simp only [RingHom.id_apply, mul_one, one_pow] at hsum
  rw [heval] at hsum
  have hp_pred : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_le
  rw [Finset.sum_range_succ', ← hp_pred, sum_range_succ] at hsum
  have hzero : (z ^ p).coeff 0 = y ^ p := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    let ev0 : B[X] →+* B :=
      Polynomial.eval₂RingHom' (RingHom.id B) 0 (fun _ => Commute.zero_right _)
    change ev0 (z ^ p) = _
    rw [map_pow]
    congr 1
    simp [ev0, z]
  have hone : z.coeff 1 = x := by simp [z]
  have htop : (z ^ p).coeff p = x ^ p := by
    have h := Polynomial.coeff_pow_of_natDegree_le (p := z) (m := p) hz
    simpa [hone] using h
  rw [hp_pred, hzero, htop] at hsum
  have hmiddle :
      ∑ j ∈ range (p - 1), (z ^ p).coeff (j + 1) =
        ∑ j ∈ range (p - 1),
          (((j + 1 : ℕ) : K)⁻¹) • jacobsonCoeff x y (p - 1) j := by
    refine sum_congr rfl fun j hj ↦ ?_
    exact coeff_generic_pow_eq_jacobson (K := K) p hp x y j (mem_range.1 hj)
  calc
    (x + y) ^ p =
        (∑ j ∈ range (p - 1), (z ^ p).coeff (j + 1)) + x ^ p + y ^ p := hsum
    _ = (∑ j ∈ range (p - 1),
          (((j + 1 : ℕ) : K)⁻¹) • jacobsonCoeff x y (p - 1) j) +
          x ^ p + y ^ p := by rw [hmiddle]
    _ = x ^ p + y ^ p + jacobsonCorrection K p x y := by
      simp only [jacobsonCorrection]
      abel

end

section DerivationJacobson

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

local instance : LieRing (Module.End K A) := LieRing.ofAssociativeRing

/-- Forgetting the Leibniz rule embeds ring derivations into linear
endomorphisms as a Lie homomorphism. -/
def derivationToEndLieHom :
    Derivation K A A →ₗ⁅K⁆ Module.End K A where
  toFun D := D.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := Derivation.commutator_coe_linear_map

theorem derivationToEndLieHom_injective :
    Function.Injective (derivationToEndLieHom (K := K) (A := A)) := by
  intro D E h
  ext a
  exact LinearMap.congr_fun h a

theorem restrictedPowerField_toEnd (p : ℕ) [CharP K p] [Fact p.Prime]
    (D : Derivation K A A) :
    derivationToEndLieHom (Derivation.restrictedPowerField D p) =
      (derivationToEndLieHom D) ^ p := by
  ext a
  simp [derivationToEndLieHom, Derivation.restrictedPowerField_apply,
    Module.End.pow_apply]

theorem restrictedPowerField_add (p : ℕ) [CharP K p] [hp : Fact p.Prime]
    (D E : Derivation K A A) :
    Derivation.restrictedPowerField (D + E) p =
      Derivation.restrictedPowerField D p +
        Derivation.restrictedPowerField E p +
          jacobsonCorrection K p D E := by
  apply derivationToEndLieHom_injective (K := K) (A := A)
  rw [restrictedPowerField_toEnd, map_add,
    add_pow_eq_add_pow_add_jacobson (K := K) (B := Module.End K A) p hp.out,
    ← restrictedPowerField_toEnd, ← restrictedPowerField_toEnd,
    ← jacobsonCorrection_map (f := derivationToEndLieHom (K := K) (A := A))]
  simp

end DerivationJacobson

section VectorFieldJacobson

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

variable {k : Type*} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} {U : X.scheme.Opens}

noncomputable local instance vectorFieldBaseModule : Module k (X.VectorField U) :=
  Module.compHom _ (algebraMap k Γ(X.scheme, U))

noncomputable def vectorFieldDerivLinearMap
    (V : X.scheme.Opens) (hV : V ≤ U) :
    X.VectorField U →ₗ[k] Derivation k Γ(X.scheme, V) Γ(X.scheme, V) where
  toFun D := D.deriv V hV
  map_add' _ _ := rfl
  map_smul' c D := by
    ext a
    change X.scheme.presheaf.map (homOfLE hV).op
        (algebraMap k Γ(X.scheme, U) c) * D.deriv V hV a =
      algebraMap k Γ(X.scheme, V) c * D.deriv V hV a
    congr 1
    change X.scheme.presheaf.map (homOfLE hV).op
        (X.baseToStructureSheaf.app (.op U) c) =
      X.baseToStructureSheaf.app (.op V) c
    have hn : X.baseToStructureSheaf.app (.op U) ≫
        X.scheme.presheaf.map (homOfLE hV).op =
          X.baseToStructureSheaf.app (.op V) := by
      rw [← X.baseToStructureSheaf.naturality (homOfLE hV).op]
      rfl
    exact congrArg (fun f => f c) hn

theorem vectorField_pPower_add (D E : X.VectorField U) :
    (D + E).pPower = D.pPower + E.pPower +
      jacobsonCorrection k (ringChar k) D E := by
  letI characteristicPrime : Fact (ringChar k).Prime :=
    CharP.char_is_prime_of_pos k (ringChar k)
  ext V hV a
  change Derivation.restrictedPowerField
      (D.deriv V hV + E.deriv V hV) (ringChar k) a = _
  rw [restrictedPowerField_add (K := k) (ringChar k)]
  change _ = _ + _ +
    (vectorFieldDerivLinearMap (X := X) V hV)
      (jacobsonCorrection k (ringChar k) D E) a
  rw [jacobsonCorrection_map_linear
    (vectorFieldDerivLinearMap (X := X) V hV)]
  · rfl
  · intro F G
    rfl

end VectorFieldJacobson

section ConnectionJacobson

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type*} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} (C : X.IntegrableConnection)
variable {U : X.scheme.Opens}

/-- The `p`-power Frobenius on an algebra over a positive-characteristic
field.  Unlike mathlib's `frobenius`, this definition also covers the zero
algebra, which occurs as the ring of sections on the empty open. -/
def fieldAlgebraFrobenius (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [NeZero (ringChar k)] : A →+* A where
  toFun a := a ^ ringChar k
  map_zero' := zero_pow (NeZero.ne (ringChar k))
  map_one' := one_pow _
  map_mul' _ _ := mul_pow _ _ _
  map_add' a b := by
    classical
    by_cases hA : Nontrivial A
    · letI : Nontrivial A := hA
      letI characteristicPrime : Fact (ringChar k).Prime :=
        CharP.char_is_prime_of_pos k (ringChar k)
      letI : CharP A (ringChar k) :=
        charP_of_injective_algebraMap (algebraMap k A).injective (ringChar k)
      exact add_pow_char a b (ringChar k)
    · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
      exact Subsingleton.elim _ _

@[simp]
theorem fieldAlgebraFrobenius_apply (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [NeZero (ringChar k)] (a : A) :
    fieldAlgebraFrobenius k A a = a ^ ringChar k := rfl

noncomputable local instance connectionVectorFieldBaseModule :
    Module k (X.VectorField U) :=
  Module.compHom _ (algebraMap k Γ(X.scheme, U))

noncomputable local instance connectionSectionBaseModule :
    Module k Γ(C.carrier, U) :=
  Module.compHom _ (algebraMap k Γ(X.scheme, U))

noncomputable def nablaBaseEnd (D : X.VectorField U) :
    Module.End k Γ(C.carrier, U) where
  toFun := C.nabla U D
  map_add' := map_add _
  map_smul' c m := by
    change C.nabla U D
        ((algebraMap k Γ(X.scheme, U) c) • m) =
      (algebraMap k Γ(X.scheme, U) c) • C.nabla U D m
    rw [C.leibniz]
    simp

@[simp]
theorem nablaBaseEnd_apply (D : X.VectorField U) (m : Γ(C.carrier, U)) :
    nablaBaseEnd C D m = C.nabla U D m := rfl

@[simp]
theorem nablaBaseEnd_pow_apply (D : X.VectorField U) (n : ℕ)
    (m : Γ(C.carrier, U)) :
    ((nablaBaseEnd C D) ^ n) m = (C.nabla U D)^[n] m := by
  rw [Module.End.pow_apply]
  rfl

noncomputable def nablaBaseLinearMap :
    X.VectorField U →ₗ[k] Module.End k Γ(C.carrier, U) where
  toFun := nablaBaseEnd C
  map_add' D E := by
    ext m
    simp [nablaBaseEnd]
  map_smul' c D := by
    ext m
    change C.nabla U ((algebraMap k Γ(X.scheme, U) c) • D) m =
      (algebraMap k Γ(X.scheme, U) c) • C.nabla U D m
    simpa using congrArg (fun N => N m) ((C.nabla U).map_smul
      (algebraMap k Γ(X.scheme, U) c) D)

@[simp]
theorem nablaBaseLinearMap_apply (D : X.VectorField U)
    (m : Γ(C.carrier, U)) :
    nablaBaseLinearMap C D m = C.nabla U D m := rfl

local instance connectionEndLieRing :
    LieRing (Module.End k Γ(C.carrier, U)) := LieRing.ofAssociativeRing

theorem nablaBaseLinearMap_bracket (D E : X.VectorField U) :
    nablaBaseLinearMap C ⁅D, E⁆ =
      ⁅nablaBaseLinearMap C D, nablaBaseLinearMap C E⁆ := by
  ext m
  exact C.flat U D E m

theorem nablaBaseEnd_add_pow (D E : X.VectorField U) :
    (nablaBaseEnd C (D + E)) ^ ringChar k =
      (nablaBaseEnd C D) ^ ringChar k +
        (nablaBaseEnd C E) ^ ringChar k +
          nablaBaseLinearMap C
            (jacobsonCorrection k (ringChar k) D E) := by
  letI characteristicPrime : Fact (ringChar k).Prime :=
    CharP.char_is_prime_of_pos k (ringChar k)
  rw [show nablaBaseEnd C (D + E) =
      nablaBaseEnd C D + nablaBaseEnd C E from
    (nablaBaseLinearMap C).map_add D E]
  rw [add_pow_eq_add_pow_add_jacobson
    (K := k) (B := Module.End k Γ(C.carrier, U))
    (ringChar k) characteristicPrime.out]
  change (nablaBaseLinearMap C D) ^ ringChar k +
      (nablaBaseLinearMap C E) ^ ringChar k +
        jacobsonCorrection k (ringChar k)
          (nablaBaseLinearMap C D) (nablaBaseLinearMap C E) =
    (nablaBaseLinearMap C D) ^ ringChar k +
      (nablaBaseLinearMap C E) ^ ringChar k +
        nablaBaseLinearMap C (jacobsonCorrection k (ringChar k) D E)
  rw [← jacobsonCorrection_map_linear (nablaBaseLinearMap C)
    (nablaBaseLinearMap_bracket C)]

theorem pCurvatureAdditive_add_vectorField (D E : X.VectorField U) :
    C.pCurvatureAdditive U (D + E) =
      C.pCurvatureAdditive U D + C.pCurvatureAdditive U E := by
  letI characteristicPrime : Fact (ringChar k).Prime :=
    CharP.char_is_prime_of_pos k (ringChar k)
  ext m
  have hpow := congrArg
    (fun N : Module.End k Γ(C.carrier, U) => N m)
    (nablaBaseEnd_add_pow C D E)
  have hpPower := congrArg (fun F : X.VectorField U => C.nabla U F m)
    (vectorField_pPower_add D E)
  simp only [nablaBaseEnd_pow_apply, LinearMap.add_apply,
    nablaBaseLinearMap_apply] at hpow
  simp only [map_add, LinearMap.add_apply] at hpPower
  simp only [SmoothScheme.IntegrableConnection.pCurvatureAdditive_apply,
    LinearMap.add_apply]
  rw [hpow, hpPower]
  abel

end

end ConnectionJacobson

section Hochschild

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Coefficients obtained by normally ordering the iterates of `a D` with
all multiplication operators placed on the left. -/
def hochschildCoeff (D : Derivation K A A) (a : A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, j + 1 =>
      a * D (hochschildCoeff D a n (j + 1)) +
        a * hochschildCoeff D a n j

@[simp]
theorem hochschildCoeff_eq_zero_of_lt (D : Derivation K A A) (a : A)
    {n j : ℕ} (h : n < j) : hochschildCoeff D a n j = 0 := by
  induction n generalizing j with
  | zero =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rfl
  | succ n ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      simp only [hochschildCoeff]
      rw [ih (by omega), ih (by omega)]
      simp

@[simp]
theorem hochschildCoeff_zero (D : Derivation K A A) (a : A) (n : ℕ) :
    hochschildCoeff D a n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [hochschildCoeff]

@[simp]
theorem derivation_hochschildCoeff_zero (D : Derivation K A A)
    (a : A) (n : ℕ) : D (hochschildCoeff D a n 0) = 0 := by
  cases n <;> simp [hochschildCoeff]

theorem sum_range_shift_of_boundary_zero {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) (hzero : f 0 = 0) (hlast : f (n + 1) = 0) :
    ∑ j ∈ range (n + 1), f (j + 1) = ∑ j ∈ range (n + 1), f j := by
  rw [sum_range_succ, sum_range_succ']
  simp [hzero, hlast]

theorem hochschildCoeff_sum_succ {M : Type*} [AddCommMonoid M]
    [Module A M] (D : Derivation K A A) (a : A) (F : ℕ → M) (n : ℕ) :
    ∑ j ∈ range (n + 2), hochschildCoeff D a (n + 1) j • F j =
      ∑ j ∈ range (n + 1),
        ((a * D (hochschildCoeff D a n j)) • F j +
          (a * hochschildCoeff D a n j) • F (j + 1)) := by
  rw [sum_range_succ']
  simp only [hochschildCoeff, zero_smul, zero_add, add_smul,
    sum_add_distrib]
  rw [sum_range_shift_of_boundary_zero
    (fun j => (a * D (hochschildCoeff D a n j)) • F j) n
    (by rw [derivation_hochschildCoeff_zero]; simp) (by simp)]
  simp

section OperatorExpansion

variable {M : Type*} [AddCommGroup M] [Module A M]

theorem smul_operator_mul_smul_pow (D : Derivation K A A)
    (N : Module.End ℤ M)
    (hN : ∀ (b : A) (m : M), N (b • m) = b • N m + D b • m)
    (a c : A) (j : ℕ) :
    (a • N) * (c • N ^ j) =
      (a * D c) • N ^ j + (a * c) • N ^ (j + 1) := by
  ext m
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply]
  rw [hN, pow_succ', Module.End.mul_apply]
  simp only [smul_add, smul_smul]
  ac_rfl

/-- Normal-ordering expansion for an iterated scalar multiple of a
connection-like additive operator. -/
theorem smul_operator_pow_eq_sum (D : Derivation K A A)
    (N : Module.End ℤ M)
    (hN : ∀ (b : A) (m : M), N (b • m) = b • N m + D b • m)
    (a : A) (n : ℕ) :
    (a • N) ^ n =
      ∑ j ∈ range (n + 1), hochschildCoeff D a n j • N ^ j := by
  induction n with
  | zero => simp [hochschildCoeff]
  | succ n ih =>
      rw [pow_succ', ih, mul_sum]
      simp_rw [smul_operator_mul_smul_pow D N hN]
      exact (hochschildCoeff_sum_succ D a (fun j => N ^ j) n).symm

end OperatorExpansion

@[simp]
theorem hochschildCoeff_diagonal (D : Derivation K A A) (a : A) (n : ℕ) :
    hochschildCoeff D a n n = a ^ n := by
  induction n with
  | zero => simp [hochschildCoeff]
  | succ n ih =>
      simp [hochschildCoeff, ih, pow_succ, mul_comm]

@[simp]
theorem hochschildCoeff_one (D : Derivation K A A) (a : A) (n : ℕ) :
    hochschildCoeff D a (n + 1) 1 = (a • D : A → A)^[n] a := by
  induction n with
  | zero => simp [hochschildCoeff]
  | succ n ih =>
      change a * D (hochschildCoeff D a (n + 1) 1) +
          a * hochschildCoeff D a (n + 1) 0 = _
      rw [ih]
      simp only [hochschildCoeff_zero, Nat.succ_ne_zero, if_false,
        mul_zero, add_zero, Function.iterate_succ_apply']
      rfl

/-- Function-valued form of the normal-ordering expansion, specialized to
a derivation. -/
theorem smul_derivation_iterate_eq_sum (D : Derivation K A A)
    (a x : A) (n : ℕ) :
    (a • D : A → A)^[n] x =
      ∑ j ∈ range (n + 1),
        hochschildCoeff D a n j * D^[j] x := by
  let N : Module.End ℤ A := D.toLinearMap.restrictScalars ℤ
  have h := congrArg (fun F : Module.End ℤ A => F x)
    (smul_operator_pow_eq_sum D N
      (fun b m => by
        change D (b * m) = b * D m + D b * m
        simpa [mul_comm] using D.leibniz b m) a n)
  simp only [Module.End.pow_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul] at h
  change (fun y => a * D y)^[n] x =
    ∑ j ∈ range (n + 1),
      hochschildCoeff D a n j * D^[j] x at h
  change (fun y => a * D y)^[n] x =
    ∑ j ∈ range (n + 1),
      hochschildCoeff D a n j * D^[j] x
  exact h

section CoefficientNaturality

variable {B : Type*} [CommRing B] [Algebra K B]

theorem hochschildCoeff_map (f : A →ₐ[K] B)
    (D : Derivation K A A) (E : Derivation K B B)
    (hDE : ∀ x, f (D x) = E (f x)) (a : A) (n j : ℕ) :
    f (hochschildCoeff D a n j) = hochschildCoeff E (f a) n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [hochschildCoeff]
  | succ n ih =>
      cases j with
      | zero => simp [hochschildCoeff]
      | succ j => simp [hochschildCoeff, ih, hDE]

end CoefficientNaturality

/-- Extend a derivation of `A` to `A[X]`, acting coefficientwise and sending
`X` to `1`. -/
noncomputable def polynomialExtension (D : Derivation K A A) :
    Derivation K A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs +
    Polynomial.derivative'.restrictScalars K

@[simp]
theorem polynomialExtension_C (D : Derivation K A A) (a : A) :
    polynomialExtension D (Polynomial.C a) = Polynomial.C (D a) := by
  simp [polynomialExtension, PolynomialModule.equivPolynomialSelf_apply_eq]

@[simp]
theorem polynomialExtension_X (D : Derivation K A A) :
    polynomialExtension D Polynomial.X = 1 := by
  simp [polynomialExtension]

@[simp]
theorem polynomialExtension_X_pow (D : Derivation K A A) (n : ℕ) :
    polynomialExtension D (Polynomial.X ^ n) =
      Polynomial.derivative (Polynomial.X ^ n : A[X]) := by
  rw [Derivation.leibniz_pow, polynomialExtension_X,
    Polynomial.derivative_X_pow]
  simp [nsmul_eq_mul]

theorem polynomialExtension_iterate_X_pow (D : Derivation K A A)
    (n j : ℕ) :
    (polynomialExtension D)^[j] (Polynomial.X ^ n) =
      Polynomial.derivative^[j] (Polynomial.X ^ n : A[X]) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rw [Polynomial.iterate_derivative_X_pow_eq_C_mul]
      simp [Polynomial.derivative_X_pow]

@[simp]
theorem hochschildCoeff_polynomialExtension (D : Derivation K A A)
    (a : A) (n j : ℕ) :
    hochschildCoeff (polynomialExtension D) (Polynomial.C a) n j =
      Polynomial.C (hochschildCoeff D a n j) := by
  have h := hochschildCoeff_map
    ((Polynomial.CAlgHom : A →ₐ[A] A[X]).restrictScalars K)
    D (polynomialExtension D) (fun x => (polynomialExtension_C D x).symm)
    a n j
  change Polynomial.C (hochschildCoeff D a n j) =
    hochschildCoeff (polynomialExtension D) (Polynomial.C a) n j at h
  exact h.symm

theorem coeff_zero_hochschild_extension_term (D : Derivation K A A)
    (a : A) (r n j : ℕ) :
    (hochschildCoeff (polynomialExtension D) (Polynomial.C a) r j *
        (polynomialExtension D)^[j] (Polynomial.X ^ n)).coeff 0 =
      if j = n then hochschildCoeff D a r n * (n.factorial : A) else 0 := by
  rw [hochschildCoeff_polynomialExtension,
    polynomialExtension_iterate_X_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_iterate_derivative]
  by_cases h : j = n
  · subst j
    simp [Nat.descFactorial_self]
  · simp [h]

/-- In prime characteristic, every genuinely intermediate coefficient in
the normal-ordering expansion of `(a D)^p` vanishes. -/
theorem hochschildCoeff_middle_eq_zero (p : ℕ) [CharP K p]
    [hp : Fact p.Prime] (D : Derivation K A A) (a : A) (n : ℕ)
    (hn2 : 2 ≤ n) (hnp : n < p) : hochschildCoeff D a p n = 0 := by
  classical
  by_cases hA : Nontrivial A
  · letI : Nontrivial A := hA
    let delta := polynomialExtension D
    let scaledDelta : Derivation K A[X] A[X] := Polynomial.C a • delta
    let restricted := Derivation.restrictedPowerField scaledDelta p
    have hn1 : n - 1 ≠ 0 := by omega
    have hconstant : (scaledDelta^[p] (Polynomial.X ^ n)).coeff 0 = 0 := by
      rw [← Derivation.restrictedPowerField_apply scaledDelta p]
      change (restricted (Polynomial.X ^ n)).coeff 0 = 0
      rw [Derivation.leibniz_pow]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [smul_eq_mul, hn1, restricted]
    have hexp := smul_derivation_iterate_eq_sum delta (Polynomial.C a)
      (Polynomial.X ^ n) p
    have hcoeff := congrArg (fun q : A[X] => q.coeff 0) hexp
    simp only [Polynomial.finsetSum_coeff] at hcoeff
    dsimp [delta] at hcoeff
    simp_rw [coeff_zero_hochschild_extension_term D a p n] at hcoeff
    change (((fun q => Polynomial.C a * polynomialExtension D q)^[p])
      (Polynomial.X ^ n)).coeff 0 = _ at hcoeff
    change (((fun q => Polynomial.C a * polynomialExtension D q)^[p])
      (Polynomial.X ^ n)).coeff 0 = 0 at hconstant
    rw [hconstant] at hcoeff
    have hnmem : n ∈ range (p + 1) := by
      exact mem_range.mpr (hnp.trans p.lt_succ_self)
    have hproduct : hochschildCoeff D a p n * (n.factorial : A) = 0 := by
      simpa [hnmem] using hcoeff.symm
    have hfacK : (n.factorial : K) ≠ 0 := by
      intro hzero
      have hdvd : p ∣ n.factorial :=
        (CharP.cast_eq_zero_iff K p n.factorial).mp hzero
      have hle : p ≤ n := hp.out.dvd_factorial.mp hdvd
      omega
    have hfacA : IsUnit (n.factorial : A) := by
      simpa using (isUnit_iff_ne_zero.mpr hfacK).map (algebraMap K A)
    exact hfacA.mul_left_eq_zero.mp hproduct
  · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    exact Subsingleton.elim _ _

/-- Hochschild's formula for a connection-like operator in prime
characteristic. -/
theorem smul_operator_pow_prime (p : ℕ) [CharP K p]
    [hp : Fact p.Prime] {M : Type*} [AddCommGroup M] [Module A M]
    (D : Derivation K A A) (N : Module.End ℤ M)
    (hN : ∀ (b : A) (m : M), N (b • m) = b • N m + D b • m)
    (a : A) :
    (a • N) ^ p =
      a ^ p • N ^ p + ((a • D : A → A)^[p - 1] a) • N := by
  classical
  rw [smul_operator_pow_eq_sum D N hN]
  let f : ℕ → Module.End ℤ M :=
    fun j => hochschildCoeff D a p j • N ^ j
  have hsubset : ({1, p} : Finset ℕ) ⊆ range (p + 1) := by
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · simp [hp.out.pos]
    · simp
  have hoff : ∀ j ∈ range (p + 1), j ∉ ({1, p} : Finset ℕ) → f j = 0 := by
    intro j hjRange hjEndpoints
    simp only [mem_insert, mem_singleton, not_or] at hjEndpoints
    rcases j with _ | _ | j
    · simp [f, hochschildCoeff, hp.out.ne_zero]
    · exact (hjEndpoints.1 rfl).elim
    · have hjp : j + 2 < p := by
        have hjle : j + 2 ≤ p := by
          have := mem_range.mp hjRange
          omega
        exact lt_of_le_of_ne hjle hjEndpoints.2
      rw [show f (j + 2) = 0 by
        simp [f, hochschildCoeff_middle_eq_zero p D a (j + 2)
          (by omega) hjp]]
  have hc : hochschildCoeff D a p 1 = (a • D : A → A)^[p - 1] a := by
    conv_lhs => rw [← Nat.sub_add_cancel hp.out.one_le]
    exact hochschildCoeff_one D a (p - 1)
  calc
    ∑ j ∈ range (p + 1), hochschildCoeff D a p j • N ^ j =
        ∑ j ∈ ({1, p} : Finset ℕ), f j :=
      (sum_subset hsubset hoff).symm
    _ = a ^ p • N ^ p + ((a • D : A → A)^[p - 1] a) • N := by
      rw [sum_insert (by simpa using hp.out.ne_one.symm), sum_singleton]
      simp [f, hc, add_comm]

theorem smul_derivation_iterate_prime (p : ℕ) [CharP K p]
    [Fact p.Prime] (D : Derivation K A A) (a x : A) :
    (a • D : A → A)^[p] x =
      a ^ p * D^[p] x + ((a • D : A → A)^[p - 1] a) * D x := by
  let N : Module.End ℤ A := D.toLinearMap.restrictScalars ℤ
  have h := congrArg (fun F : Module.End ℤ A => F x)
    (smul_operator_pow_prime p D N
      (fun b m => by
        change D (b * m) = b * D m + D b * m
        simpa [mul_comm] using D.leibniz b m) a)
  simp only [Module.End.pow_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at h
  change (fun y => a * D y)^[p] x =
    a ^ p * D^[p] x + ((fun y => a * D y)^[p - 1] a) * D x at h
  change (fun y => a * D y)^[p] x =
    a ^ p * D^[p] x + ((fun y => a * D y)^[p - 1] a) * D x
  exact h

/-- Hochschild's scalar formula for the restricted power of a derivation. -/
theorem restrictedPowerField_smul (p : ℕ) [CharP K p]
    [Fact p.Prime] (D : Derivation K A A) (a : A) :
    Derivation.restrictedPowerField (a • D) p =
      a ^ p • Derivation.restrictedPowerField D p +
        ((a • D : A → A)^[p - 1] a) • D := by
  ext x
  simp only [Derivation.restrictedPowerField_apply, Derivation.add_apply,
    Derivation.smul_apply]
  exact smul_derivation_iterate_prime p D a x

end Hochschild

section VectorFieldHochschild

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

variable {k : Type*} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} {U : X.scheme.Opens}

theorem vectorField_restrict_smul_act_iterate (D : X.VectorField U)
    (V : X.scheme.Opens) (hV : V ≤ U) (a b : Γ(X.scheme, U)) (n : ℕ) :
    X.scheme.presheaf.map (homOfLE hV).op
        ((a • D.act : Γ(X.scheme, U) → Γ(X.scheme, U))^[n] b) =
      ((X.scheme.presheaf.map (homOfLE hV).op a • D.deriv V hV :
        Γ(X.scheme, V) → Γ(X.scheme, V))^[n])
        (X.scheme.presheaf.map (homOfLE hV).op b) := by
  apply LSZ.map_iterate
  intro c
  change X.scheme.presheaf.map (homOfLE hV).op (a * D.act c) =
    X.scheme.presheaf.map (homOfLE hV).op a *
      D.deriv V hV (X.scheme.presheaf.map (homOfLE hV).op c)
  rw [map_mul, D.compatible le_rfl hV c]

/-- Hochschild's scalar formula for the restricted power of a vector
field. -/
theorem vectorField_pPower_smul (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    (a • D).pPower = a ^ ringChar k • D.pPower +
      ((a • D.act : Γ(X.scheme, U) → Γ(X.scheme, U))^[ringChar k - 1] a) • D := by
  letI characteristicPrime : Fact (ringChar k).Prime :=
    CharP.char_is_prime_of_pos k (ringChar k)
  ext V hV b
  change Derivation.restrictedPowerField
      (X.scheme.presheaf.map (homOfLE hV).op a • D.deriv V hV)
        (ringChar k) b = _
  rw [restrictedPowerField_smul]
  simp only [SmoothScheme.VectorField.add_deriv,
    SmoothScheme.VectorField.smul_deriv,
    SmoothScheme.VectorField.pPower_deriv,
    Derivation.add_apply, Derivation.smul_apply]
  rw [map_pow]
  rw [vectorField_restrict_smul_act_iterate D V hV a a (ringChar k - 1)]

end VectorFieldHochschild

section ConnectionHochschild

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type*} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} (C : X.IntegrableConnection)
variable {U : X.scheme.Opens}

theorem connection_smul_pow (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    (C.nabla U (a • D)) ^ ringChar k =
      a ^ ringChar k • (C.nabla U D) ^ ringChar k +
        ((a • D.act : Γ(X.scheme, U) → Γ(X.scheme, U))^[ringChar k - 1] a) •
          C.nabla U D := by
  letI characteristicPrime : Fact (ringChar k).Prime :=
    CharP.char_is_prime_of_pos k (ringChar k)
  rw [(C.nabla U).map_smul]
  exact smul_operator_pow_prime (ringChar k) D.act (C.nabla U D)
    (C.leibniz U D) a

/-- Scalar half of Frobenius semilinearity of p-curvature. -/
theorem pCurvatureAdditive_smul_vectorField (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    C.pCurvatureAdditive U (a • D) =
      a ^ ringChar k • C.pCurvatureAdditive U D := by
  simp only [SmoothScheme.IntegrableConnection.pCurvatureAdditive]
  rw [connection_smul_pow C a D, vectorField_pPower_smul a D]
  simp only [map_add, map_smul]
  module

/-- P-curvature is Frobenius-semilinear in its vector-field argument,
expressed as an equality of `O(U)`-linear endomorphisms. -/
theorem pCurvature_smul_vectorField (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    C.pCurvature U (a • D) =
      a ^ ringChar k • C.pCurvature U D := by
  ext m
  exact congrArg (fun F : Module.End ℤ Γ(C.carrier, U) => F m)
    (pCurvatureAdditive_smul_vectorField C a D)

theorem pCurvature_add_vectorField (D E : X.VectorField U) :
    C.pCurvature U (D + E) = C.pCurvature U D + C.pCurvature U E := by
  ext m
  exact congrArg (fun F : Module.End ℤ Γ(C.carrier, U) => F m)
    (pCurvatureAdditive_add_vectorField C D E)

/-- P-curvature bundled as a Frobenius-semilinear map in the vector-field
argument.  Its additive field is supplied by
`pCurvature_add_vectorField`, not inferred from scalar homogeneity. -/
def pCurvatureFrobeniusSemilinear (U : X.scheme.Opens) :
    X.VectorField U →ₛₗ[fieldAlgebraFrobenius k Γ(X.scheme, U)]
      Module.End Γ(X.scheme, U) Γ(C.carrier, U) where
  toFun := C.pCurvature U
  map_add' := pCurvature_add_vectorField C
  map_smul' := pCurvature_smul_vectorField C

@[simp]
theorem pCurvatureFrobeniusSemilinear_apply (U : X.scheme.Opens)
    (D : X.VectorField U) :
    pCurvatureFrobeniusSemilinear C U D = C.pCurvature U D := rfl

end

end ConnectionHochschild

end LSZ
