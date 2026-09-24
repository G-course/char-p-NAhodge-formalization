import LSZ.AffineLSZ
import LSZ.RestrictedIdentities
import LSZ.WordNilpotence
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Nilpotence of the affine LSZ p-curvature

This file contains the nilpotent part of the affine calculation.  The
nilpotence hypothesis is the LSZ convention used throughout the project:
every word of length `p` in arbitrary Higgs contractions is zero.  The
conclusion is proved from the connection constructed in `AffineLSZ`; it is
not stored as an extra field of that connection.
-/

open CategoryTheory
open scoped ModuleCat.Algebra ChangeOfRings TensorProduct

namespace LSZ

universe u

noncomputable section

section JacobsonAbelianIdeal

variable {K Q B : Type*} [Field K]
variable [AddCommGroup Q] [Module K Q]
variable [Ring B] [Algebra K B]

local instance : LieRing B := LieRing.ofAssociativeRing

/-- In an abelian ideal stable under `ad x`, the coefficients occurring in
Jacobson's formula have only one nonzero diagonal term. -/
lemma jacobsonCoeff_eq_of_abelian_ideal
    (x : B) (L : Q →ₗ[K] Q) (iota : Q →ₗ[K] B)
    (hx : ∀ q, ⁅x, iota q⁆ = iota (L q))
    (hab : ∀ q r, ⁅iota q, iota r⁆ = 0)
    (z : Q) (n i : Nat) :
    jacobsonCoeff x (iota z) (n + 1) i =
      if i + 1 = n + 1 then iota (-L^[n + 1] z) else 0 := by
  induction n generalizing i with
  | zero =>
      cases i with
      | zero =>
          simp only [jacobsonCoeff]
          calc
            ⁅iota z, x⁆ = -⁅x, iota z⁆ := by
              exact (lie_skew (iota z) x).symm
            _ = -iota (L z) := by rw [hx]
            _ = iota (-L z) := by rw [map_neg]
      | succ i =>
          cases i with
          | zero => simp [jacobsonCoeff]
          | succ i => simp [jacobsonCoeff]
  | succ n ih =>
      cases i with
      | zero =>
          rw [jacobsonCoeff, ih]
          have hout : ¬0 + 1 = n + 1 + 1 := by omega
          rw [if_neg hout]
          by_cases hprev : 0 + 1 = n + 1
          · rw [if_pos hprev, map_neg, lie_neg, hab, neg_zero]
          · rw [if_neg hprev, lie_zero]
      | succ i =>
          rw [jacobsonCoeff, ih (i + 1), ih i]
          by_cases hdiag : i = n
          · have hupper : ¬i + 1 + 1 = n + 1 := by omega
            have hmiddle : i + 1 = n + 1 := by omega
            have hout : i + 1 + 1 = n + 1 + 1 := by omega
            rw [if_neg hupper, if_pos hmiddle, if_pos hout, lie_zero,
              zero_add, hx]
            simp only [map_neg]
            congr 2
            simp only [Function.iterate_succ_apply']
          · have hmiddle : ¬i + 1 = n + 1 := by omega
            have hout : ¬i + 1 + 1 = n + 1 + 1 := by omega
            by_cases hupper : i + 1 + 1 = n + 1
            · rw [if_pos hupper, if_neg hmiddle, if_neg hout, lie_zero,
                add_zero, map_neg, lie_neg, hab, neg_zero]
            · rw [if_neg hupper, if_neg hmiddle, if_neg hout]
              simp only [lie_zero, zero_add]

/-- Jacobson's entire correction is the final iterated adjoint when the
second summand lies in an abelian ideal stable under `ad x`. -/
lemma jacobsonCorrection_eq_of_abelian_ideal
    {p : Nat} [CharP K p] [hp : Fact p.Prime]
    (x : B) (L : Q →ₗ[K] Q) (iota : Q →ₗ[K] B)
    (hx : ∀ q, ⁅x, iota q⁆ = iota (L q))
    (hab : ∀ q r, ⁅iota q, iota r⁆ = 0)
    (z : Q) :
    jacobsonCorrection K p x (iota z) = iota (L^[p - 1] z) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpred : (p - 2) + 1 = p - 1 := by omega
  have hmem : p - 2 ∈ Finset.range (p - 1) := by
    simp only [Finset.mem_range]
    omega
  have hcast : ((p - 1 : Nat) : K) = -1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one,
      CharP.cast_eq_zero K p, zero_sub]
  rw [jacobsonCorrection, Finset.sum_eq_single (p - 2)]
  · have hc := jacobsonCoeff_eq_of_abelian_ideal
      x L iota hx hab z (p - 2) (p - 2)
    rw [hpred] at hc
    simp only [if_true] at hc
    rw [hc, hpred, hcast]
    simp only [inv_neg, inv_one, neg_smul, map_neg, one_smul, neg_neg]
  · intro j hj hne
    have hjne : j + 1 ≠ p - 1 := by
      intro h
      have : j = p - 2 := by omega
      exact hne this
    have hc := jacobsonCoeff_eq_of_abelian_ideal
      x L iota hx hab z (p - 2) j
    rw [hpred] at hc
    rw [hc, if_neg hjne, smul_zero]
  · exact fun h => (h hmem).elim

lemma jacobsonCoeff_eq_zero_of_commute
    (x y : B) (hxy : Commute x y) (n i : Nat) :
    jacobsonCoeff x y (n + 1) i = 0 := by
  induction n generalizing i with
  | zero =>
      cases i with
      | zero =>
          simp only [jacobsonCoeff, Ring.lie_def]
          rw [hxy.eq]
          exact sub_self _
      | succ i =>
          cases i with
          | zero => simp [jacobsonCoeff, Ring.lie_def]
          | succ i => simp [jacobsonCoeff]
  | succ n ih =>
      cases i with
      | zero =>
          rw [jacobsonCoeff, ih 0, lie_zero]
      | succ i =>
          rw [jacobsonCoeff, ih (i + 1), ih i, lie_zero, lie_zero, add_zero]

/-- Frobenius additivity for commuting elements of a `K`-algebra.  Unlike
`add_pow_char_of_commute`, this does not require the algebra map to be
injective, so it also applies to endomorphisms of the zero module. -/
lemma add_pow_eq_add_pow_of_commute_algebra
    {p : Nat} [CharP K p] [Fact p.Prime]
    (x y : B) (hxy : Commute x y) :
    (x + y) ^ p = x ^ p + y ^ p := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpred : (p - 2) + 1 = p - 1 := by omega
  have hcorr : jacobsonCorrection K p x y = 0 := by
    rw [jacobsonCorrection]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← hpred, jacobsonCoeff_eq_zero_of_commute x y hxy, smul_zero]
  rw [add_pow_eq_add_pow_add_jacobson (K := K) (B := B)
    p Fact.out x y, hcorr, add_zero]

end JacobsonAbelianIdeal

lemma wordApply_congr
    {T S M : Type*} (act : T → M → M) (act' : S → M → M)
    (f : T → S) (h : ∀ t m, act t m = act' (f t) m)
    (n : Nat) (v : Fin n → T) (m : M) :
    wordApply act n v m = wordApply act' n (fun i => f (v i)) m := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change act (v 0) (wordApply act n (fun i => v i.succ) m) =
        act' (f (v 0))
          (wordApply act' n (fun i => f (v i.succ)) m)
      rw [h]
      exact congrArg (act' (f (v 0))) (ih (fun i => v i.succ))

lemma wordApply_zero_of_map_zero
    {T M : Type*} [Zero M] (act : T → M → M)
    (hzero : ∀ t, act t 0 = 0) (n : Nat) (v : Fin n → T) :
    wordApply act n v 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change act (v 0) (wordApply act n (fun i => v i.succ) 0) = 0
      rw [ih, hzero]

namespace AffineObject

variable (k : Type u) (A : Type u) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [CharP k p] [Fact p.Prime]

/-- A finite-projective affine Higgs bundle with LSZ nilpotence level at
most `p - 1`.  Nilpotence means that every word of exactly `p` arbitrary
tangent contractions vanishes. -/
structure NilpotentHiggs extends IntegrableHiggs k A where
  finite : Module.Finite A carrier
  projective : Module.Projective A carrier
  nilpotent : IsWordNilpotent p (fun D m => theta D m)

namespace NilpotentHiggs

variable {k A p}

/-- Forget finite projectivity and the nilpotence proof. -/
abbrev toIntegrable (E : NilpotentHiggs k A p) : IntegrableHiggs k A :=
  E.toIntegrableHiggs

instance (E : NilpotentHiggs k A p) : Module.Finite A E.carrier := E.finite

instance (E : NilpotentHiggs k A p) : Module.Projective A E.carrier := E.projective

/-- Morphisms in the nilpotent Higgs category are exactly morphisms of the
underlying integrable Higgs modules. -/
abbrev Hom (E F : NilpotentHiggs k A p) :=
  E.toIntegrable ⟶ F.toIntegrable

instance : Category (NilpotentHiggs k A p) where
  Hom := Hom
  id E := 𝟙 E.toIntegrable
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget finite projectivity and word nilpotence. -/
def forget : NilpotentHiggs k A p ⥤ IntegrableHiggs k A where
  obj E := E.toIntegrable
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end NilpotentHiggs

namespace IntegrableConnection

variable {k A p}

/-- The standard-sign p-curvature of an affine integrable connection. -/
def pCurvature (C : IntegrableConnection k A) (p : ℕ)
    [CharP k p] [Fact p.Prime] (D : Tangent k A) : Module.End k C.carrier :=
  C.nabla D ^ p - C.nabla (Derivation.restrictedPowerField D p)

@[simp]
lemma pCurvature_apply (C : IntegrableConnection k A) (p : ℕ)
    [CharP k p] [Fact p.Prime] (D : Tangent k A) (m : C.carrier) :
    C.pCurvature p D m =
      (C.nabla D)^[p] m - C.nabla (Derivation.restrictedPowerField D p) m := by
  change ((C.nabla D) ^ p) m -
      C.nabla (Derivation.restrictedPowerField D p) m = _
  rw [Module.End.pow_apply]

end IntegrableConnection

/-- An affine integrable connection whose p-curvature satisfies the strong
LSZ nilpotence condition: every word of length `p` in arbitrary
p-curvature contractions is zero. -/
structure NilpotentFlat extends IntegrableConnection k A where
  finite : Module.Finite A carrier
  projective : Module.Projective A carrier
  nilpotentPCurvature :
    IsWordNilpotent p
      (fun D m ↦ toIntegrableConnection.pCurvature p D m)

namespace NilpotentFlat

variable {k A p}

/-- Forget the p-curvature nilpotence proof. -/
abbrev toIntegrable (E : NilpotentFlat k A p) : IntegrableConnection k A :=
  E.toIntegrableConnection

instance (E : NilpotentFlat k A p) : Module.Finite A E.carrier := E.finite

instance (E : NilpotentFlat k A p) : Module.Projective A E.carrier := E.projective

/-- Morphisms in the nilpotent flat category are horizontal morphisms of
the underlying connections. -/
abbrev Hom (E F : NilpotentFlat k A p) :=
  E.toIntegrable ⟶ F.toIntegrable

instance : Category (NilpotentFlat k A p) where
  Hom := Hom
  id E := 𝟙 E.toIntegrable
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget p-curvature nilpotence. -/
def forget : NilpotentFlat k A p ⥤ IntegrableConnection k A where
  obj E := E.toIntegrable
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end NilpotentFlat

end AffineObject

namespace AffineFrobeniusLift

variable (k : Type u) (A : Type u) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [CharP k p] [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- The additive carrier identification hidden inside mathlib's
restriction-of-scalars object.  It is used only to name the first tensor
coefficient in the finite-generation proof below. -/
private def unrestrictSelfAddEquiv (f : A →+* A) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of A A) ≃+ A :=
  AddEquiv.refl A

set_option backward.isDefEq.respectTransparency false in
/-- Frobenius extension of scalars preserves finite generation for the
finite-projective Higgs carriers used by LSZ. -/
theorem pullback_finite
    (E : AffineObject.NilpotentHiggs k A p) :
    Module.Finite A (pullback k A p E.carrier) := by
  classical
  obtain ⟨s, hs⟩ := E.finite.fg_top
  let t : Finset (pullback k A p E.carrier) :=
    s.image (fun m ↦ StandardFrobeniusPullback.tmul
      k A E.carrier p 1 m)
  refine ⟨⟨t, Submodule.eq_top_iff'.2 ?_⟩⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a m =>
      let a' : A :=
        unrestrictSelfAddEquiv A (algebraFrobenius k A p) a
      have hm : m ∈ Submodule.span A (↑s : Set E.carrier) := by
        rw [hs]
        exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem m hm =>
          change StandardFrobeniusPullback.tmul
              k A E.carrier p a' m ∈ _
          have ha : StandardFrobeniusPullback.tmul
                k A E.carrier p a' m =
              a' • StandardFrobeniusPullback.tmul
                k A E.carrier p 1 m := by
            simpa only [mul_one] using
              (StandardFrobeniusPullback.smul_tmul
                k A E.carrier p a' 1 m).symm
          rw [ha]
          exact Submodule.smul_mem _ a'
            (Submodule.subset_span (by
              change StandardFrobeniusPullback.tmul
                  k A E.carrier p 1 m ∈ ↑t
              exact Finset.mem_coe.mpr
                (Finset.mem_image.mpr ⟨m, hm, rfl⟩)))
      | zero =>
          rw [TensorProduct.tmul_zero]
          exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ ihx ihy
      | smul b m hm ih =>
          change StandardFrobeniusPullback.tmul
              k A E.carrier p a' (b • m) ∈ _
          rw [tmul_smul]
          exact Submodule.smul_mem _ (algebraFrobenius k A p b) ih

/-- Frobenius extension of scalars preserves projectivity.  The proof uses
the extension--restriction adjunction and mathlib's categorical
characterization of projective modules. -/
theorem pullback_projective
    (E : AffineObject.NilpotentHiggs k A p) :
    Module.Projective A (pullback k A p E.carrier) := by
  let f := algebraFrobenius k A p
  let F := ModuleCat.extendScalars f
  let G := ModuleCat.restrictScalars f
  letI : G.PreservesEpimorphisms :=
    { preserves := by
        intro X Y g hg
        rw [ModuleCat.epi_iff_surjective] at hg ⊢
        exact hg }
  letI : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj f)
  have hE : CategoryTheory.Projective E.carrier := inferInstance
  have hF : CategoryTheory.Projective (F.obj E.carrier) :=
    F.projective_obj_of_projective hE
  exact ModuleCat.projective_of_module_projective (F.obj E.carrier)

namespace DividedDifferential

/-- The Cartier restricted identity satisfied by the dual of
`d F_tilde / p`.  It is separated from the definition of the connection:
flatness only uses closedness, while the exact p-curvature formula uses this
additional identity. -/
def SatisfiesCartier
    (Z : DividedDifferential k A p) : Prop :=
  forall D : Tangent k A,
    (StandardFrobeniusPullback.canonicalNabla
        k A (Tangent k A) p D)^[p - 1] (Z.zeta D) -
      Z.zeta (Derivation.restrictedPowerField D p) =
        -StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 D

end DividedDifferential

lemma AffineObject.NilpotentHiggs.theta_pow_eq_zero
    (E : AffineObject.NilpotentHiggs k A p) (D : Tangent k A) :
    (E.theta D) ^ p = 0 := by
  simpa using E.nilpotent.twoBlock_exact
    (fun V => E.theta V) D D (i := p) (j := 0) (by simp)

lemma pulledEnd_iterate_tmul
    (E : AffineObject.NilpotentHiggs k A p) (D : Tangent k A)
    (n : Nat) (a : A) (m : E.carrier) :
    (pulledEnd k A p E.toIntegrable D)^[n]
        (StandardFrobeniusPullback.tmul k A E.carrier p a m) =
      StandardFrobeniusPullback.tmul k A E.carrier p a
        ((E.theta D)^[n] m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pulledEnd_tmul]
      change StandardFrobeniusPullback.tmul k A E.carrier p a
          (E.theta D ((E.theta D)^[n] m)) = _
      rw [Function.iterate_succ_apply']

lemma pulledEnd_wordApply_tmul
    (E : AffineObject.NilpotentHiggs k A p)
    (n : Nat) (v : Fin n → Tangent k A) (a : A) (m : E.carrier) :
    wordApply
        (fun D x => pulledEnd k A p E.toIntegrable D x) n v
        (StandardFrobeniusPullback.tmul k A E.carrier p a m) =
      StandardFrobeniusPullback.tmul k A E.carrier p a
        (wordApply (fun D x => E.theta D x) n v m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pulledEnd k A p E.toIntegrable (v 0)
          (wordApply
            (fun D x => pulledEnd k A p E.toIntegrable D x) n
            (fun i => v i.succ)
            (StandardFrobeniusPullback.tmul k A E.carrier p a m)) = _
      rw [ih, pulledEnd_tmul]
      rfl

lemma pulledEnd_wordApply_add
    (E : AffineObject.IntegrableHiggs k A)
    (n : Nat) (v : Fin n → Tangent k A)
    (x y : pullback k A p E.carrier) :
    wordApply (fun D z => pulledEnd k A p E D z) n v (x + y) =
      wordApply (fun D z => pulledEnd k A p E D z) n v x +
        wordApply (fun D z => pulledEnd k A p E D z) n v y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pulledEnd k A p E (v 0)
          (wordApply (fun D z => pulledEnd k A p E D z) n
            (fun i => v i.succ) (x + y)) = _
      rw [ih, map_add]
      rfl

/-- Frobenius extension of scalars preserves the full LSZ word-nilpotence
condition, not merely the p-th power of one contraction. -/
lemma pulledEnd_wordNilpotent
    (E : AffineObject.NilpotentHiggs k A p) :
    IsWordNilpotent p
      (fun D x => pulledEnd k A p E.toIntegrable D x) := by
  intro v x
  induction x using TensorProduct.induction_on with
  | zero =>
      change wordApply
          (fun D z => pulledEnd k A p E.toIntegrable D z) p v
          (0 : pullback k A p E.carrier) = 0
      exact wordApply_zero_of_map_zero
        (fun D z => pulledEnd k A p E.toIntegrable D z)
        (fun D => LinearMap.map_zero (pulledEnd k A p E.toIntegrable D)) p v
  | tmul a m =>
      let a' : A := a
      let m' : E.carrier := m
      change wordApply
          (fun D z => pulledEnd k A p E.toIntegrable D z) p v
          (StandardFrobeniusPullback.tmul k A E.carrier p a' m') = 0
      rw [pulledEnd_wordApply_tmul, E.nilpotent v m]
      exact StandardFrobeniusPullback.tmul_zero k A E.carrier p a'
  | add x y hx hy =>
      let x' : pullback k A p E.carrier := x
      let y' : pullback k A p E.carrier := y
      change wordApply
          (fun D z => pulledEnd k A p E.toIntegrable D z) p v (x' + y') = 0
      rw [pulledEnd_wordApply_add, hx, hy, add_zero]

/-- A single pulled-back Higgs contraction has p-th power zero.  This is a
theorem about mathlib's actual extension-of-scalars module. -/
lemma pulledEnd_pow_eq_zero
    (E : AffineObject.NilpotentHiggs k A p) (D : Tangent k A) :
    (pulledEnd k A p E.toIntegrable D) ^ p = 0 := by
  simpa using (pulledEnd_wordNilpotent k A p E).twoBlock_exact
    (fun V => pulledEnd k A p E.toIntegrable V) D D
    (i := p) (j := 0) (by simp)

lemma pulledEnd_neg
    (E : AffineObject.IntegrableHiggs k A) (D : Tangent k A) :
    pulledEnd k A p E (-D) = -pulledEnd k A p E D := by
  exact (thetaUnit k A p E).hom.map_neg D

/-- The pulled-back Higgs action, regarded as a `k`-linear endomorphism. -/
def pulledAction (E : AffineObject.IntegrableHiggs k A)
    (q : pullback k A p (tangentModule k A)) :
    Module.End k (pullback k A p E.carrier) :=
  (pullbackTheta k A p E q).restrictScalars k

/-- Linearity of the pulled Higgs action in its pulled tangent argument. -/
def pulledActionLinear (E : AffineObject.IntegrableHiggs k A) :
    pullback k A p (tangentModule k A) →ₗ[k]
      Module.End k (pullback k A p E.carrier) :=
  ((DividedDifferential.restrictEnd k A (pullback k A p E.carrier)).comp
    (pullbackTheta k A p E)).restrictScalars k

@[simp]
lemma pulledActionLinear_apply
    (E : AffineObject.IntegrableHiggs k A)
    (q : pullback k A p (tangentModule k A)) :
    pulledActionLinear k A p E q = pulledAction k A p E q := rfl

@[simp]
lemma pulledAction_zero (E : AffineObject.IntegrableHiggs k A) :
    pulledAction k A p E 0 = 0 := by
  rfl

lemma pulledAction_add (E : AffineObject.IntegrableHiggs k A)
    (q r : pullback k A p (tangentModule k A)) :
    pulledAction k A p E (q + r) =
      pulledAction k A p E q + pulledAction k A p E r := by
  exact map_add (pulledActionLinear k A p E) q r

lemma pulledAction_neg (E : AffineObject.IntegrableHiggs k A)
    (q : pullback k A p (tangentModule k A)) :
    pulledAction k A p E (-q) = -pulledAction k A p E q := by
  exact map_neg (pulledActionLinear k A p E) q

@[simp]
lemma pulledAction_tmul_apply
    (E : AffineObject.IntegrableHiggs k A) (a : A) (D : Tangent k A)
    (x : pullback k A p E.carrier) :
    pulledAction k A p E
        (StandardFrobeniusPullback.tmul k A (Tangent k A) p a D) x =
      a • pulledEnd k A p E D x := by
  rfl

lemma pulledAction_commute
    (E : AffineObject.IntegrableHiggs k A)
    (q r : pullback k A p (tangentModule k A)) :
    Commute (pulledAction k A p E q) (pulledAction k A p E r) := by
  change pulledAction k A p E q * pulledAction k A p E r =
    pulledAction k A p E r * pulledAction k A p E q
  apply LinearMap.ext
  intro x
  exact pullbackTheta_commutes k A p E q r x

lemma pulledAction_bracket_eq_zero
    (E : AffineObject.IntegrableHiggs k A)
    (q r : pullback k A p (tangentModule k A)) :
    ⁅pulledAction k A p E q, pulledAction k A p E r⁆ = 0 := by
  letI : LieRing (Module.End k (pullback k A p E.carrier)) :=
    LieRing.ofAssociativeRing
  rw [Ring.lie_def, sub_eq_zero]
  exact (pulledAction_commute k A p E q r).eq

/-- The product of `n` pulled-back Higgs contractions, bundled as an
`A`-multilinear map in the pulled tangent vectors. -/
def pulledActionWordMultilinear
    (E : AffineObject.IntegrableHiggs k A) (n : Nat) :
    MultilinearMap A
      (fun _ : Fin n => pullback k A p (tangentModule k A))
      (Module.End A (pullback k A p E.carrier)) :=
  (MultilinearMap.mkPiAlgebraFin A n
      (Module.End A (pullback k A p E.carrier))).compLinearMap
    (fun _ => pullbackTheta k A p E)

lemma pulledActionWordMultilinear_apply
    (E : AffineObject.IntegrableHiggs k A) (n : Nat)
    (v : Fin n → pullback k A p (tangentModule k A))
    (x : pullback k A p E.carrier) :
    pulledActionWordMultilinear k A p E n v x =
      wordApply (fun q y => pullbackTheta k A p E q y) n v x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (List.ofFn
          (fun i : Fin (n + 1) => pullbackTheta k A p E (v i))).prod x = _
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      change pullbackTheta k A p E (v 0)
          ((List.ofFn (fun i : Fin n =>
            pullbackTheta k A p E (v i.succ))).prod x) =
        pullbackTheta k A p E (v 0)
          (wordApply (fun q y => pullbackTheta k A p E q y) n
            (fun i => v i.succ) x)
      apply congrArg (pullbackTheta k A p E (v 0))
      exact ih (fun i => v i.succ)

/-- The pure tensors `1 ⊗ D` span the Frobenius pullback of the tangent
module over the target ring. -/
lemma pullbackTangent_span_eq_top :
    Submodule.span A
      (Set.range (fun D : Tangent k A =>
        StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 D)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro q
  induction q using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a D =>
      let a' : A := a
      let D' : Tangent k A := D
      change StandardFrobeniusPullback.tmul
          k A (Tangent k A) p a' D' ∈ _
      have hgen : StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 D' ∈
          Submodule.span A
            (Set.range (fun V : Tangent k A =>
              StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 V)) :=
        Submodule.subset_span ⟨D', rfl⟩
      have hsmul := (Submodule.span A
        (Set.range (fun V : Tangent k A =>
          StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 V))).smul_mem a' hgen
      have heq : a' • StandardFrobeniusPullback.tmul
          k A (Tangent k A) p 1 D' =
          StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D' := by
        simpa only [mul_one] using
          StandardFrobeniusPullback.smul_tmul
            k A (Tangent k A) p a' 1 D'
      rw [heq] at hsmul
      exact hsmul
  | add q r hq hr => exact Submodule.add_mem _ hq hr

lemma pulledAction_wordApply_one_tmul
    (E : AffineObject.IntegrableHiggs k A) (n : Nat)
    (v : Fin n → Tangent k A) (x : pullback k A p E.carrier) :
    wordApply (fun q y => pullbackTheta k A p E q y) n
        (fun i => StandardFrobeniusPullback.tmul
          k A (Tangent k A) p 1 (v i)) x =
      wordApply (fun D y => pulledEnd k A p E D y) n v x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pullbackTheta k A p E
          (StandardFrobeniusPullback.tmul
            k A (Tangent k A) p 1 (v 0))
          (wordApply (fun q y => pullbackTheta k A p E q y) n
            (fun i => StandardFrobeniusPullback.tmul
              k A (Tangent k A) p 1 (v i.succ)) x) = _
      rw [pullbackTheta_tmul, one_smul, ih (fun i => v i.succ)]
      rfl

/-- Strong word-nilpotence survives Frobenius extension of scalars even
when every argument is an arbitrary element of the pulled tangent module. -/
lemma pulledActionWordMultilinear_eq_zero
    (E : AffineObject.NilpotentHiggs k A p) :
    pulledActionWordMultilinear k A p E.toIntegrable p = 0 := by
  apply MultilinearMap.ext_of_span_eq_top
    (g := fun {_ : Fin p} (D : Tangent k A) =>
      StandardFrobeniusPullback.tmul k A (Tangent k A) p 1 D)
    (fun _ => pullbackTangent_span_eq_top k A p)
  intro v
  apply LinearMap.ext
  intro x
  rw [pulledActionWordMultilinear_apply]
  change wordApply
      (fun q y => pullbackTheta k A p E.toIntegrable q y) p
      (fun i => StandardFrobeniusPullback.tmul
        k A (Tangent k A) p 1 (v i)) x = 0
  rw [pulledAction_wordApply_one_tmul]
  exact pulledEnd_wordNilpotent k A p E v x

/-- The pulled-back Higgs action satisfies the original strong LSZ
nilpotence condition for arbitrary pulled tangent vectors. -/
lemma pulledAction_wordNilpotent
    (E : AffineObject.NilpotentHiggs k A p) :
    IsWordNilpotent p
      (fun q x => pulledAction k A p E.toIntegrable q x) := by
  intro v x
  change wordApply
      (fun q y => pullbackTheta k A p E.toIntegrable q y) p v x = 0
  rw [← pulledActionWordMultilinear_apply]
  exact LinearMap.congr_fun
    (MultilinearMap.congr_fun
      (pulledActionWordMultilinear_eq_zero k A p E) v) x

/-- Commuting the canonical derivative past a pulled Higgs contraction
differentiates only its pulled tangent coefficient. -/
lemma canonicalNabla_bracket_pulledAction
    (E : AffineObject.IntegrableHiggs k A) (D : Tangent k A)
    (q : pullback k A p (tangentModule k A)) :
    ⁅StandardFrobeniusPullback.canonicalNabla k A E.carrier p D,
        pulledAction k A p E q⁆ =
      pulledAction k A p E
        (StandardFrobeniusPullback.canonicalNabla
          k A (Tangent k A) p D q) := by
  letI : LieRing (Module.End k (pullback k A p E.carrier)) :=
    LieRing.ofAssociativeRing
  apply LinearMap.ext
  intro x
  simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply]
  have h := canonicalNabla_pullbackTheta k A p E D q x
  change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
      (pulledAction k A p E q x) =
    pulledAction k A p E
        (StandardFrobeniusPullback.canonicalNabla
          k A (Tangent k A) p D q) x +
      pulledAction k A p E q
        (StandardFrobeniusPullback.canonicalNabla
          k A E.carrier p D x) at h
  rw [h]
  abel

lemma pulledAction_tmul_iterate
    (E : AffineObject.IntegrableHiggs k A) (a : A) (D : Tangent k A)
    (n : Nat) (x : pullback k A p E.carrier) :
    (pulledAction k A p E
      (StandardFrobeniusPullback.tmul k A (Tangent k A) p a D))^[n] x =
        a ^ n • (pulledEnd k A p E D)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pulledAction_tmul_apply,
        map_smul, pow_succ, mul_smul]
      rw [Function.iterate_succ_apply', smul_smul, mul_comm a (a ^ n)]
      rw [smul_smul]

/-- The full pulled-back Higgs action still has p-th power zero, including
for a non-pure element of the Frobenius-pulled tangent module. -/
lemma pulledAction_pow_eq_zero
    (E : AffineObject.NilpotentHiggs k A p)
    (q : pullback k A p (tangentModule k A)) :
    (pulledAction k A p E.toIntegrable q) ^ p = 0 := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change (pulledAction k A p E.toIntegrable 0) ^ p = 0
      rw [pulledAction_zero]
      exact zero_pow ((Fact.out : p.Prime).ne_zero)
  | tmul a D =>
      apply LinearMap.ext
      intro x
      simp only [Module.End.pow_apply, LinearMap.zero_apply]
      let a' : A := a
      let D' : Tangent k A := D
      change (pulledAction k A p E.toIntegrable
        (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D'))^[p] x = 0
      rw [pulledAction_tmul_iterate]
      have h := LinearMap.congr_fun (pulledEnd_pow_eq_zero k A p E D') x
      simp only [Module.End.pow_apply, LinearMap.zero_apply] at h
      rw [h, smul_zero]
  | add q r hq hr =>
      let q' : pullback k A p (tangentModule k A) := q
      let r' : pullback k A p (tangentModule k A) := r
      change (pulledAction k A p E.toIntegrable (q' + r')) ^ p = 0
      rw [pulledAction_add,
        add_pow_eq_add_pow_of_commute_algebra (K := k)
          (pulledAction k A p E.toIntegrable q')
          (pulledAction k A p E.toIntegrable r')
          (pulledAction_commute k A p E.toIntegrable q' r'), hq, hr, add_zero]

lemma canonicalNabla_iterate_tmul (M : ModuleCat.{u} A)
    (D : Tangent k A) (n : Nat) (a : A) (m : M) :
    (StandardFrobeniusPullback.canonicalNabla k A M p D)^[n]
        (StandardFrobeniusPullback.tmul k A M p a m) =
      StandardFrobeniusPullback.tmul k A M p (D^[n] a) m := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        StandardFrobeniusPullback.canonicalNabla_tmul]
      rw [Function.iterate_succ_apply']

/-- The canonical Cartier connection has zero p-curvature. -/
lemma canonicalNabla_pow (M : ModuleCat.{u} A) (D : Tangent k A) :
    (StandardFrobeniusPullback.canonicalNabla k A M p D) ^ p =
      StandardFrobeniusPullback.canonicalNabla k A M p
        (Derivation.restrictedPowerField D p) := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.pow_apply]
  induction x using TensorProduct.induction_on with
  | zero =>
      change (StandardFrobeniusPullback.canonicalNabla k A M p D)^[p]
          (0 : StandardFrobeniusPullback.obj k A M p) =
        StandardFrobeniusPullback.canonicalNabla k A M p
          (Derivation.restrictedPowerField D p) 0
      rw [iterate_map_zero, map_zero]
  | tmul a m =>
      let a' : A := a
      let m' : M := m
      change (StandardFrobeniusPullback.canonicalNabla k A M p D)^[p]
          (StandardFrobeniusPullback.tmul k A M p a' m') =
        StandardFrobeniusPullback.canonicalNabla k A M p
          (Derivation.restrictedPowerField D p)
          (StandardFrobeniusPullback.tmul k A M p a' m')
      rw [canonicalNabla_iterate_tmul,
        StandardFrobeniusPullback.canonicalNabla_tmul,
        Derivation.restrictedPowerField_apply]
  | add x y hx hy =>
      let x' : StandardFrobeniusPullback.obj k A M p := x
      let y' : StandardFrobeniusPullback.obj k A M p := y
      change (StandardFrobeniusPullback.canonicalNabla k A M p D)^[p]
          (x' + y') =
        StandardFrobeniusPullback.canonicalNabla k A M p
          (Derivation.restrictedPowerField D p) (x' + y')
      rw [iterate_map_add, map_add, hx, hy]

/-- The standard-sign p-curvature of the affine LSZ connection. -/
def pCurvature (Z : DividedDifferential k A p)
    (E : AffineObject.IntegrableHiggs k A) (D : Tangent k A) :
    Module.End k (pullback k A p E.carrier) :=
  (Z.nabla k A p E D) ^ p -
    Z.nabla k A p E (Derivation.restrictedPowerField D p)

/-- The pulled tangent vector measuring the Cartier restricted-power
identity for a divided differential. -/
def cartierDefect (Z : DividedDifferential k A p) (D : Tangent k A) :
    pullback k A p (tangentModule k A) :=
  (StandardFrobeniusPullback.canonicalNabla
      k A (Tangent k A) p D)^[p - 1] (Z.zeta D) -
    Z.zeta (Derivation.restrictedPowerField D p)

/-- Before imposing the exact Cartier identity, p-curvature is the
pulled-back Higgs action evaluated on the Cartier defect. -/
theorem pCurvature_eq_pulledAction_cartierDefect
    (Z : DividedDifferential k A p)
    (E : AffineObject.NilpotentHiggs k A p) (D : Tangent k A) :
    pCurvature k A p Z E.toIntegrable D =
      pulledAction k A p E.toIntegrable (cartierDefect k A p Z D) := by
  let P := pullback k A p E.carrier
  let Q := pullback k A p (tangentModule k A)
  let canM : Module.End k P :=
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
  let canQ : Module.End k Q :=
    StandardFrobeniusPullback.canonicalNabla k A (Tangent k A) p D
  let act : Q →ₗ[k] Module.End k P :=
    pulledActionLinear k A p E.toIntegrable
  let z : Q := Z.zeta D
  let Dp : Tangent k A := Derivation.restrictedPowerField D p
  letI : LieRing (Module.End k P) := LieRing.ofAssociativeRing
  have hcan : canM ^ p =
      StandardFrobeniusPullback.canonicalNabla k A E.carrier p Dp := by
    exact canonicalNabla_pow k A p E.carrier D
  have hact : (act z) ^ p = 0 := by
    exact pulledAction_pow_eq_zero k A p E z
  have hstable : ∀ q : Q, ⁅canM, act q⁆ = act (canQ q) := by
    intro q
    exact canonicalNabla_bracket_pulledAction k A p E.toIntegrable D q
  have hab : ∀ q r : Q, ⁅act q, act r⁆ = 0 := by
    intro q r
    exact pulledAction_bracket_eq_zero k A p E.toIntegrable q r
  have hjac : jacobsonCorrection k p canM (act z) =
      act (canQ^[p - 1] z) := by
    exact jacobsonCorrection_eq_of_abelian_ideal
      canM canQ act hstable hab z
  unfold pCurvature
  change (canM + act z) ^ p -
      (StandardFrobeniusPullback.canonicalNabla
        k A E.carrier p Dp + act (Z.zeta Dp)) = _
  rw [add_pow_eq_add_pow_add_jacobson (K := k)
      (B := Module.End k P) p (Fact.out : p.Prime) canM (act z),
    hcan, hact, hjac]
  change _ = act (canQ^[p - 1] z - Z.zeta Dp)
  rw [map_sub]
  abel

/-- For a nilpotent Higgs bundle, the p-curvature is minus the Frobenius
pullback of the original Higgs contraction.  This is the affine Cartier
formula with the standard sign convention `nabla_D^p - nabla_(D^[p])`. -/
theorem pCurvature_eq_neg_pulledEnd
    (Z : DividedDifferential k A p)
    (hZ : Z.SatisfiesCartier)
    (E : AffineObject.NilpotentHiggs k A p) (D : Tangent k A) :
    pCurvature k A p Z E.toIntegrable D =
      -(pulledEnd k A p E.toIntegrable D).restrictScalars k := by
  let P := pullback k A p E.carrier
  let Q := pullback k A p (tangentModule k A)
  let canM : Module.End k P :=
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
  let canQ : Module.End k Q :=
    StandardFrobeniusPullback.canonicalNabla k A (Tangent k A) p D
  let act : Q →ₗ[k] Module.End k P :=
    pulledActionLinear k A p E.toIntegrable
  let z : Q := Z.zeta D
  let Dp : Tangent k A := Derivation.restrictedPowerField D p
  letI : LieRing (Module.End k P) := LieRing.ofAssociativeRing
  have hcan : canM ^ p =
      StandardFrobeniusPullback.canonicalNabla k A E.carrier p Dp := by
    exact canonicalNabla_pow k A p E.carrier D
  have hact : (act z) ^ p = 0 := by
    exact pulledAction_pow_eq_zero k A p E z
  have hstable : ∀ q : Q, ⁅canM, act q⁆ = act (canQ q) := by
    intro q
    exact canonicalNabla_bracket_pulledAction k A p E.toIntegrable D q
  have hab : ∀ q r : Q, ⁅act q, act r⁆ = 0 := by
    intro q r
    exact pulledAction_bracket_eq_zero k A p E.toIntegrable q r
  have hjac : jacobsonCorrection k p canM (act z) =
      act (canQ^[p - 1] z) := by
    exact jacobsonCorrection_eq_of_abelian_ideal
      canM canQ act hstable hab z
  unfold pCurvature
  change (canM + act z) ^ p -
      (StandardFrobeniusPullback.canonicalNabla
        k A E.carrier p Dp + act (Z.zeta Dp)) = _
  rw [add_pow_eq_add_pow_add_jacobson (K := k)
      (B := Module.End k P) p (Fact.out : p.Prime) canM (act z),
    hcan, hact, hjac]
  calc
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p Dp + 0 +
          act (canQ^[p - 1] z) -
        (StandardFrobeniusPullback.canonicalNabla k A E.carrier p Dp +
          act (Z.zeta Dp)) =
        act (canQ^[p - 1] z) - act (Z.zeta Dp) := by abel
    _ = act (canQ^[p - 1] z - Z.zeta Dp) := by
      rw [map_sub]
    _ = act (-StandardFrobeniusPullback.tmul
          k A (Tangent k A) p 1 D) := by
      rw [hZ D]
    _ = -(pulledEnd k A p E.toIntegrable D).restrictScalars k := by
      apply LinearMap.ext
      intro x
      change pulledAction k A p E.toIntegrable
          (-StandardFrobeniusPullback.tmul
            k A (Tangent k A) p 1 D) x =
        -(pulledEnd k A p E.toIntegrable D x)
      rw [pulledAction_neg, LinearMap.neg_apply,
        pulledAction_tmul_apply, one_smul]

/-- The LSZ connection attached to a nilpotent Higgs bundle has nilpotent
p-curvature in the same strong word sense: every composite of `p`
possibly different p-curvature contractions is zero. -/
theorem pCurvature_wordNilpotent
    (Z : DividedDifferential k A p)
    (E : AffineObject.NilpotentHiggs k A p) :
    IsWordNilpotent p
      (fun D x => pCurvature k A p Z E.toIntegrable D x) := by
  intro v x
  rw [wordApply_congr
    (fun D y => pCurvature k A p Z E.toIntegrable D y)
    (fun q y => pulledAction k A p E.toIntegrable q y)
    (fun D => cartierDefect k A p Z D)]
  · exact pulledAction_wordNilpotent k A p E
      (fun i => cartierDefect k A p Z (v i)) x
  · intro D y
    exact LinearMap.congr_fun
      (pCurvature_eq_pulledAction_cartierDefect k A p Z E D) y

end AffineFrobeniusLift

end

end LSZ
