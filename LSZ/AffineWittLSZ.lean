import LSZ.AffineWittLift

/-!
# The affine LSZ functor attached to an actual Frobenius lift

This file starts with a smooth `W₂(k)`-algebra and a ring endomorphism
lifting Frobenius.  It packages the divided differential constructed in
`AffineWittLift` into the affine LSZ functor and proves the corresponding
word-nilpotence statement for p-curvature.
-/

open Function
open CategoryTheory
open scoped ModuleCat.Algebra ChangeOfRings TensorProduct

namespace LSZ

universe u

noncomputable section

namespace AffineWittLift.Frobenius

variable (p : ℕ) (k B : Type u)
variable [Field k] [CharP k p] [Fact p.Prime] [PerfectField k]
variable [CommRing B] [Algebra (W₂ p k) B]
variable [Algebra.Smooth (W₂ p k) B]

variable (Phi : AffineWittLift.Frobenius p k B)

private abbrev A := AffineWittLift.SpecialFiber p k B

@[simp]
lemma frobeniusDualBaseChangeEquiv_tmul_apply_tmul
    (a b : A p k B)
    (phi : Module.Dual (A p k B) Ω[A p k B⁄k])
    (omega : Ω[A p k B⁄k]) :
    frobeniusDualBaseChangeEquiv p k B
        (StandardFrobeniusPullback.tmul k (A p k B)
          (Module.Dual (A p k B) Ω[A p k B⁄k]) p a phi)
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p b omega) =
      a * (algebraFrobenius k (A p k B) p (phi omega) * b) := by
  rfl

/-- Evaluation between Frobenius pullbacks of tangent and cotangent modules,
transported through finite-projective dual base change. -/
def frobeniusPairing
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) : A p k B :=
  frobeniusDualBaseChangeEquiv p k B
    ((pullbackCotangentDualEquivTangent p k B).symm v) omega

@[simp]
lemma frobeniusPairing_zero_left
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B 0 omega = 0 := by
  rw [frobeniusPairing, map_zero, map_zero, LinearMap.zero_apply]

@[simp]
lemma frobeniusPairing_add_left
    (v w : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B (v + w) omega =
      frobeniusPairing p k B v omega +
        frobeniusPairing p k B w omega := by
  rw [frobeniusPairing, map_add, map_add, LinearMap.add_apply]
  rfl

@[simp]
lemma frobeniusPairing_sub_left
    (v w : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B (v - w) omega =
      frobeniusPairing p k B v omega -
        frobeniusPairing p k B w omega := by
  rw [frobeniusPairing, map_sub, map_sub, LinearMap.sub_apply]
  rfl

@[simp]
lemma frobeniusPairing_zero_right
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B))) :
    frobeniusPairing p k B v 0 = 0 := by
  rw [frobeniusPairing, map_zero]

@[simp]
lemma frobeniusPairing_add_right
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (omega eta : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B v (omega + eta) =
      frobeniusPairing p k B v omega +
        frobeniusPairing p k B v eta := by
  rw [frobeniusPairing, map_add]
  rfl

@[simp]
lemma frobeniusPairing_smul_right
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (a : A p k B)
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B v (a • omega) =
      a • frobeniusPairing p k B v omega := by
  rw [frobeniusPairing, map_smul]
  rfl

@[simp]
lemma frobeniusPairing_tmul_tmul
    (a b : A p k B) (D : Tangent k (A p k B))
    (omega : Ω[A p k B⁄k]) :
    frobeniusPairing p k B
        (StandardFrobeniusPullback.tmul k (A p k B)
          (Tangent k (A p k B)) p a D)
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p b omega) =
      a * (algebraFrobenius k (A p k B) p
        (((cotangentDualEquivTangent p k B).symm D) omega) * b) := by
  rfl

/-- The dual divided Frobenius is characterized by transposition against the
divided cotangent morphism. -/
lemma frobeniusPairing_dividedFrobeniusZeta
    (D : Tangent k (A p k B))
    (omega : AffineFrobeniusLift.pullback k (A p k B) p
      (ModuleCat.of (A p k B) Ω[A p k B⁄k])) :
    frobeniusPairing p k B (dividedFrobeniusZeta p k B Phi D) omega =
      ((cotangentDualEquivTangent p k B).symm D)
        (dividedFrobeniusCotangent p k B Phi omega) := by
  rw [frobeniusPairing, dividedFrobeniusZeta]
  simp only [LinearMap.comp_apply]
  change (frobeniusDualBaseChangeEquiv p k B)
      ((pullbackCotangentDualEquivTangent p k B).symm
        ((pullbackCotangentDualEquivTangent p k B)
          ((frobeniusDualBaseChangeEquiv p k B).symm
            ((dividedFrobeniusCotangent p k B Phi).dualMap
              ((cotangentDualEquivTangent p k B).symm D))))) omega = _
  rw [(pullbackCotangentDualEquivTangent p k B).symm_apply_apply,
    (frobeniusDualBaseChangeEquiv p k B).apply_symm_apply]
  rfl

@[simp]
lemma frobeniusPairing_dividedFrobeniusZeta_tmul_D
    (D : Tangent k (A p k B)) (b : A p k B) :
    frobeniusPairing p k B (dividedFrobeniusZeta p k B Phi D)
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1
            (KaehlerDifferential.D k (A p k B) b)) =
      ((cotangentDualEquivTangent p k B).symm D)
        (specialFiberDividedDifferentialForm p k B Phi b) := by
  rw [frobeniusPairing_dividedFrobeniusZeta,
    dividedFrobeniusCotangent_tmul_D, one_smul]

/-- Derivations kill the image of absolute Frobenius. -/
lemma tangent_algebraFrobenius_eq_zero
    (D : Tangent k (A p k B)) (a : A p k B) :
    D (algebraFrobenius k (A p k B) p a) = 0 := by
  rw [algebraFrobenius_apply, Derivation.leibniz_pow]
  have hpA : (p : A p k B) = 0 := by
    calc
      (p : A p k B) = algebraMap k (A p k B) (p : k) :=
        (map_natCast (algebraMap k (A p k B)) p).symm
      _ = algebraMap k (A p k B) 0 := by
        rw [CharP.cast_eq_zero]
      _ = 0 := map_zero _
  rw [← Nat.cast_smul_eq_nsmul (A p k B), hpA, zero_smul]

/-- Under the Frobenius pairing, the canonical connection differentiates
only the coefficient of a pulled-back tangent vector. -/
lemma frobeniusPairing_canonicalNabla_tmul_one
    (D : Tangent k (A p k B))
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B)))
    (omega : Ω[A p k B⁄k]) :
    frobeniusPairing p k B
        (StandardFrobeniusPullback.canonicalNabla k (A p k B)
          (Tangent k (A p k B)) p D v)
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1 omega) =
      D (frobeniusPairing p k B v
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1 omega)) := by
  induction v using TensorProduct.induction_on with
  | zero =>
      change frobeniusPairing p k B
          (StandardFrobeniusPullback.canonicalNabla k (A p k B)
            (Tangent k (A p k B)) p D 0)
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega) =
        D (frobeniusPairing p k B 0
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega))
      rw [map_zero, frobeniusPairing_zero_left, map_zero]
  | tmul a phi =>
      let a' : A p k B := a
      let phi' : Tangent k (A p k B) := phi
      change frobeniusPairing p k B
          (StandardFrobeniusPullback.canonicalNabla k (A p k B)
            (Tangent k (A p k B)) p D
              (StandardFrobeniusPullback.tmul k (A p k B)
                (Tangent k (A p k B)) p a' phi'))
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega) =
        D (frobeniusPairing p k B
          (StandardFrobeniusPullback.tmul k (A p k B)
            (Tangent k (A p k B)) p a' phi')
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega))
      rw [StandardFrobeniusPullback.canonicalNabla_tmul,
        frobeniusPairing_tmul_tmul, frobeniusPairing_tmul_tmul]
      rw [mul_one]
      change D a' * (algebraFrobenius k (A p k B) p)
          (((cotangentDualEquivTangent p k B).symm phi') omega) =
        D (a' * (algebraFrobenius k (A p k B) p)
          (((cotangentDualEquivTangent p k B).symm phi') omega))
      rw [Derivation.leibniz, tangent_algebraFrobenius_eq_zero]
      change D a' * _ = a' * 0 + _ * D a'
      rw [mul_zero, zero_add, mul_comm]
  | add x y hx hy =>
      let x' : AffineFrobeniusLift.pullback k (A p k B) p
          (AffineFrobeniusLift.tangentModule k (A p k B)) := x
      let y' : AffineFrobeniusLift.pullback k (A p k B) p
          (AffineFrobeniusLift.tangentModule k (A p k B)) := y
      change frobeniusPairing p k B
          (StandardFrobeniusPullback.canonicalNabla k (A p k B)
            (Tangent k (A p k B)) p D (x' + y'))
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega) =
        D (frobeniusPairing p k B (x' + y')
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega))
      rw [map_add, frobeniusPairing_add_left,
        frobeniusPairing_add_left, map_add, hx, hy]

/-- Pairing with `1 ⊗ omega`, packaged as an `A`-linear map into the
Frobenius-twisted scalar module. -/
def frobeniusPairingUnitLinear
    (v : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B))) :
    Ω[A p k B⁄k] →ₗ[A p k B]
      AffineWittLift.FrobeniusTwist k (A p k B) (A p k B) p where
  toFun omega := AffineWittLift.FrobeniusTwist.mk
    (frobeniusPairing p k B v
      (StandardFrobeniusPullback.tmul k (A p k B)
        Ω[A p k B⁄k] p 1 omega))
  map_add' := by
    intro omega eta
    apply AffineWittLift.FrobeniusTwist.ext
    change frobeniusPairing p k B v
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1 (omega + eta)) = _
    rw [StandardFrobeniusPullback.tmul_add,
      frobeniusPairing_add_right,
      AffineWittLift.FrobeniusTwist.down_add,
      AffineWittLift.FrobeniusTwist.down_mk,
      AffineWittLift.FrobeniusTwist.down_mk]
  map_smul' := by
    intro a omega
    apply AffineWittLift.FrobeniusTwist.ext
    change frobeniusPairing p k B v
        (StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1 (a • omega)) =
      algebraFrobenius k (A p k B) p a •
        frobeniusPairing p k B v
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega)
    have htmul : StandardFrobeniusPullback.tmul k (A p k B)
          Ω[A p k B⁄k] p 1 (a • omega) =
        algebraFrobenius k (A p k B) p a •
          StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1 omega :=
      AffineFrobeniusLift.tmul_smul k (A p k B) p
        (ModuleCat.of (A p k B) Ω[A p k B⁄k]) 1 a omega
    rw [htmul, frobeniusPairing_smul_right]

/-- Pulled tangent vectors are determined by their Frobenius pairing with
the pulled universal differentials `1 ⊗ d b`. -/
lemma frobeniusPairing_left_ext_D
    {v w : AffineFrobeniusLift.pullback k (A p k B) p
      (AffineFrobeniusLift.tangentModule k (A p k B))}
    (h : ∀ b : A p k B,
      frobeniusPairing p k B v
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1
              (KaehlerDifferential.D k (A p k B) b)) =
        frobeniusPairing p k B w
          (StandardFrobeniusPullback.tmul k (A p k B)
            Ω[A p k B⁄k] p 1
              (KaehlerDifferential.D k (A p k B) b))) :
    v = w := by
  have hunit : frobeniusPairingUnitLinear p k B v =
      frobeniusPairingUnitLinear p k B w := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro b
    apply AffineWittLift.FrobeniusTwist.ext
    exact h b
  apply (pullbackCotangentDualEquivTangent p k B).symm.injective
  apply (frobeniusDualBaseChangeEquiv p k B).injective
  let fv := frobeniusDualBaseChangeEquiv p k B
    ((pullbackCotangentDualEquivTangent p k B).symm v)
  let fw := frobeniusDualBaseChangeEquiv p k B
    ((pullbackCotangentDualEquivTangent p k B).symm w)
  have hfg : ModuleCat.ofHom fv = ModuleCat.ofHom fw := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro omega
    have hu := LinearMap.congr_fun hunit omega
    exact congrArg AffineWittLift.FrobeniusTwist.down hu
  exact congrArg ModuleCat.Hom.hom hfg

/-- Reduction from the lift to the special fibre preserves powers. -/
lemma toSpecialFiber_pow (b : B) (n : ℕ) :
    WittLengthTwo.toSpecialFiber p k (b ^ n) =
      (WittLengthTwo.toSpecialFiber p k b : A p k B) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, WittLengthTwo.toSpecialFiber_apply]
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, toSpecialFiber_mul, ih]

/-- The base-change identification for Kähler differentials carries a
reduced universal differential to the universal differential of the reduced
element. -/
lemma specialFiberKaehlerEquiv_toSpecialFiber_D (b : B) :
    specialFiberKaehlerEquiv p k B
        (WittLengthTwo.toSpecialFiber p k
          (KaehlerDifferential.D (W₂ p k) B b)) =
      KaehlerDifferential.D k (A p k B)
        (WittLengthTwo.toSpecialFiber p k b) := by
  letI : Algebra B (A p k B) := Algebra.TensorProduct.rightAlgebra
  rw [WittLengthTwo.toSpecialFiber_apply,
    WittLengthTwo.toSpecialFiber_apply]
  change KaehlerDifferential.tensorKaehlerEquivBase
      (W₂ p k) k B (A p k B)
        ((1 : k) ⊗ₜ[W₂ p k] KaehlerDifferential.D (W₂ p k) B b) = _
  rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

/-- Every divided-Frobenius one-form is the sum of the universal Cartier
term `a^(p-1) d a` and an exact form.  The second summand depends on a lift,
so the theorem records only its existence. -/
lemma exists_specialFiberDividedDifferentialForm_eq
    (a : A p k B) :
    ∃ h : A p k B,
      specialFiberDividedDifferentialForm p k B Phi a =
        a ^ (p - 1) • KaehlerDifferential.D k (A p k B) a +
          KaehlerDifferential.D k (A p k B) h := by
  obtain ⟨b, rfl⟩ := toSpecialFiber_surjective p k B a
  letI : Module.Flat (W₂ p k) B := inferInstance
  have hzero : WittLengthTwo.toSpecialFiber p k (Phi.map b - b ^ p) = 0 := by
    rw [map_sub, toSpecialFiber_map_eq_pow, toSpecialFiber_pow, sub_self]
  obtain ⟨c, hc⟩ :=
    WittLengthTwo.exists_eq_p_smul_of_toSpecialFiber_eq_zero
      p k (Phi.map b - b ^ p) hzero
  refine ⟨WittLengthTwo.toSpecialFiber p k c, ?_⟩
  have hPhi : Phi.map b = b ^ p + (p : W₂ p k) • c := by
    calc
      Phi.map b = (Phi.map b - b ^ p) + b ^ p := by abel
      _ = (p : W₂ p k) • c + b ^ p := by rw [hc]
      _ = b ^ p + (p : W₂ p k) • c := add_comm _ _
  have hDsmul : KaehlerDifferential.D (W₂ p k) B ((p : W₂ p k) • c) =
      (p : W₂ p k) • KaehlerDifferential.D (W₂ p k) B c :=
    (KaehlerDifferential.D (W₂ p k) B).toLinearMap.map_smul
      (p : W₂ p k) c
  have hraw : rawDifferential p k B Phi b =
      (p : W₂ p k) •
        (b ^ (p - 1) • KaehlerDifferential.D (W₂ p k) B b +
          KaehlerDifferential.D (W₂ p k) B c) := by
    rw [rawDifferential_apply, hPhi, map_add,
      Derivation.leibniz_pow, hDsmul,
      ← Nat.cast_smul_eq_nsmul (W₂ p k), smul_add]
  rw [specialFiberDividedDifferentialForm_toSpecialFiber,
    dividedDifferential_eq_of_rawDifferential_eq_p_smul
      p k B Phi b _ hraw]
  rw [map_add (WittLengthTwo.toSpecialFiber
      (M := Ω[B⁄W₂ p k]) p k),
    map_add (specialFiberKaehlerEquiv p k B),
    specialFiberKaehlerEquiv_toSpecialFiber_smul,
    specialFiberKaehlerEquiv_toSpecialFiber_D,
    specialFiberKaehlerEquiv_toSpecialFiber_D,
    toSpecialFiber_pow]

@[simp]
lemma cotangentDualEquivTangent_symm_apply_D
    (D : Tangent k (A p k B)) (a : A p k B) :
    ((cotangentDualEquivTangent p k B).symm D)
        (KaehlerDifferential.D k (A p k B) a) = D a :=
  Derivation.liftKaehlerDifferential_comp_D D a

@[simp]
lemma cotangentContraction_cartier_add_exact
    (a h : A p k B) (D : Tangent k (A p k B)) :
    ((cotangentDualEquivTangent p k B).symm D)
        (a ^ (p - 1) • KaehlerDifferential.D k (A p k B) a +
          KaehlerDifferential.D k (A p k B) h) =
      a ^ (p - 1) * D a + D h := by
  rw [map_add, map_smul,
    cotangentDualEquivTangent_symm_apply_D,
    cotangentDualEquivTangent_symm_apply_D]
  rfl

/-- The Cartier term `a^(p-1) d a` and every exact form are closed under
the derivation-bracket test used by the LSZ flatness calculation. -/
lemma contraction_closed_cartier_add_exact
    (a h : A p k B) (D E : Tangent k (A p k B)) :
    ((cotangentDualEquivTangent p k B).symm ⁅D, E⁆)
        (a ^ (p - 1) • KaehlerDifferential.D k (A p k B) a +
          KaehlerDifferential.D k (A p k B) h) =
      D (((cotangentDualEquivTangent p k B).symm E)
          (a ^ (p - 1) • KaehlerDifferential.D k (A p k B) a +
            KaehlerDifferential.D k (A p k B) h)) -
        E (((cotangentDualEquivTangent p k B).symm D)
          (a ^ (p - 1) • KaehlerDifferential.D k (A p k B) a +
            KaehlerDifferential.D k (A p k B) h)) := by
  rw [cotangentContraction_cartier_add_exact,
    cotangentContraction_cartier_add_exact,
    cotangentContraction_cartier_add_exact,
    Derivation.commutator_apply, Derivation.commutator_apply,
    map_add, map_add,
    Derivation.leibniz, Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.leibniz_pow]
  simp only [smul_eq_mul]
  ring

/-- The dual of the actual divided Frobenius differential is closed. -/
lemma dividedFrobeniusZeta_closed
    (D E : Tangent k (A p k B)) :
    dividedFrobeniusZeta p k B Phi ⁅D, E⁆ =
      StandardFrobeniusPullback.canonicalNabla k (A p k B)
          (Tangent k (A p k B)) p D
          (dividedFrobeniusZeta p k B Phi E) -
        StandardFrobeniusPullback.canonicalNabla k (A p k B)
          (Tangent k (A p k B)) p E
          (dividedFrobeniusZeta p k B Phi D) := by
  apply frobeniusPairing_left_ext_D p k B
  intro b
  rw [frobeniusPairing_dividedFrobeniusZeta_tmul_D,
    frobeniusPairing_sub_left,
    frobeniusPairing_canonicalNabla_tmul_one,
    frobeniusPairing_canonicalNabla_tmul_one,
    frobeniusPairing_dividedFrobeniusZeta_tmul_D,
    frobeniusPairing_dividedFrobeniusZeta_tmul_D]
  obtain ⟨h, hh⟩ :=
    exists_specialFiberDividedDifferentialForm_eq p k B Phi b
  rw [hh]
  exact contraction_closed_cartier_add_exact p k B b h D E

/-- The divided differential determined by the actual `W₂(k)` Frobenius
lift.  Its closedness, rather than an additional user-supplied hypothesis,
is the preceding theorem. -/
def dividedDifferentialData :
    AffineFrobeniusLift.DividedDifferential k (A p k B) p where
  zeta := dividedFrobeniusZeta p k B Phi
  closed := dividedFrobeniusZeta_closed p k B Phi

@[simp]
lemma dividedDifferentialData_zeta (D : Tangent k (A p k B)) :
    (dividedDifferentialData p k B Phi).zeta D =
      dividedFrobeniusZeta p k B Phi D := rfl

/-- The affine LSZ connection obtained from a genuine Frobenius lift and
an unrestricted integrable Higgs module. -/
def connection (E : AffineObject.IntegrableHiggs k (A p k B)) :
    AffineObject.IntegrableConnection k (A p k B) :=
  AffineFrobeniusLift.DividedDifferential.connection
    k (A p k B) p (dividedDifferentialData p k B Phi) E

/-- On an affine chart the underlying module is precisely extension of
scalars along absolute Frobenius. -/
@[simp]
lemma connection_carrier
    (E : AffineObject.IntegrableHiggs k (A p k B)) :
    (connection p k B Phi E).carrier =
      AffineFrobeniusLift.pullback k (A p k B) p E.carrier := rfl

/-- The covariant derivative of the connection constructed from the
Frobenius lift is the canonical Cartier derivative plus the divided-
Frobenius Higgs correction. -/
@[simp]
lemma connection_nabla_apply
    (E : AffineObject.IntegrableHiggs k (A p k B))
    (D : Tangent k (A p k B))
    (x : AffineFrobeniusLift.pullback k (A p k B) p E.carrier) :
    (connection p k B Phi E).nabla D x =
      StandardFrobeniusPullback.canonicalNabla
          k (A p k B) E.carrier p D x +
        AffineFrobeniusLift.pullbackTheta k (A p k B) p E
          (dividedFrobeniusZeta p k B Phi D) x := rfl

/-- The affine LSZ functor attached to the actual Frobenius lift. -/
def functor :
    AffineObject.IntegrableHiggs k (A p k B) ⥤
      AffineObject.IntegrableConnection k (A p k B) :=
  AffineFrobeniusLift.DividedDifferential.functor
    k (A p k B) p (dividedDifferentialData p k B Phi)

@[simp]
lemma functor_obj (E : AffineObject.IntegrableHiggs k (A p k B)) :
    (functor p k B Phi).obj E = connection p k B Phi E := rfl

/-- The p-curvature of the connection produced by the genuine Frobenius
lift, written directly in terms of that connection. -/
def pCurvature (E : AffineObject.IntegrableHiggs k (A p k B))
    (D : Tangent k (A p k B)) :
    Module.End k (connection p k B Phi E).carrier :=
  ((connection p k B Phi E).nabla D) ^ p -
    (connection p k B Phi E).nabla
      (Derivation.restrictedPowerField D p)

lemma pCurvature_eq_affine
    (E : AffineObject.IntegrableHiggs k (A p k B))
    (D : Tangent k (A p k B)) :
    pCurvature p k B Phi E D =
      AffineFrobeniusLift.pCurvature k (A p k B) p
        (dividedDifferentialData p k B Phi) E D := rfl

/-- If every word of length `p` in the original Higgs contractions is
zero, then every word of length `p` in the p-curvature contractions of the
connection constructed from the Frobenius lift is zero. -/
theorem pCurvature_wordNilpotent
    (E : AffineObject.NilpotentHiggs k (A p k B) p) :
    IsWordNilpotent p
      (fun D x => pCurvature p k B Phi E.toIntegrable D x) := by
  intro v x
  change wordApply
      (fun D y => AffineFrobeniusLift.pCurvature k (A p k B) p
        (dividedDifferentialData p k B Phi) E.toIntegrable D y)
      p v x = 0
  exact AffineFrobeniusLift.pCurvature_wordNilpotent
    k (A p k B) p (dividedDifferentialData p k B Phi) E v x

/-- The connection produced from a nilpotent Higgs bundle, bundled with
the proved strong nilpotence of its p-curvature. -/
def nilpotentConnection
    (E : AffineObject.NilpotentHiggs k (A p k B) p) :
    AffineObject.NilpotentFlat k (A p k B) p where
  toIntegrableConnection := connection p k B Phi E.toIntegrable
  finite := AffineFrobeniusLift.pullback_finite
    k (A p k B) p E
  projective := AffineFrobeniusLift.pullback_projective
    k (A p k B) p E
  nilpotentPCurvature := by
    change IsWordNilpotent p
      (fun D x ↦ pCurvature p k B Phi E.toIntegrable D x)
    exact pCurvature_wordNilpotent p k B Phi E

@[simp]
lemma nilpotentConnection_toIntegrable
    (E : AffineObject.NilpotentHiggs k (A p k B) p) :
    (nilpotentConnection p k B Phi E).toIntegrable =
      connection p k B Phi E.toIntegrable := rfl

/-- On morphisms, the nilpotent LSZ transform is the same Frobenius
extension-of-scalars map as the unrestricted affine transform. -/
def nilpotentMap
    {E G : AffineObject.NilpotentHiggs k (A p k B) p} (f : E ⟶ G) :
    nilpotentConnection p k B Phi E ⟶
      nilpotentConnection p k B Phi G :=
  (functor p k B Phi).map f

/-- The genuine affine LSZ functor on the strong nilpotent categories. -/
def nilpotentFunctor :
    AffineObject.NilpotentHiggs k (A p k B) p ⥤
      AffineObject.NilpotentFlat k (A p k B) p where
  obj := nilpotentConnection p k B Phi
  map := nilpotentMap p k B Phi
  map_id E := (functor p k B Phi).map_id E.toIntegrable
  map_comp f g := (functor p k B Phi).map_comp f g

@[simp]
lemma nilpotentFunctor_obj
    (E : AffineObject.NilpotentHiggs k (A p k B) p) :
    (nilpotentFunctor p k B Phi).obj E =
      nilpotentConnection p k B Phi E := rfl

/-- Forgetting nilpotence before or after the actual affine LSZ transform
gives the same unrestricted connection functor. -/
lemma nilpotentFunctor_forget :
    nilpotentFunctor p k B Phi ⋙ AffineObject.NilpotentFlat.forget =
      AffineObject.NilpotentHiggs.forget ⋙ functor p k B Phi := rfl

end AffineWittLift.Frobenius

end

end LSZ
