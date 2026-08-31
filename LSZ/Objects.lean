import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.Derivation.Lie

/-!
# The two affine object classes in the Lan--Sheng--Zuo correspondence

This file defines the object-level data on a smooth affine chart `Spec A`.
We use `Derivation k A A` for the tangent module.  The geometric sheaf
definitions will be obtained later by localization and gluing.

The nilpotence convention is made completely explicit: “level at most
`p - 1`” means that every word of length `p` in tangent-vector actions is
zero.  On the flat side the action in this condition is the `p`-curvature,
not the connection itself.
-/

namespace LSZ

universe u₁ u₂ u₃

/-- The tangent module of the affine `k`-algebra `A`. -/
abbrev Tangent (k : Type u₁) (A : Type u₂)
    [CommRing k] [CommRing A] [Algebra k A] :=
  Derivation k A A

/-- Apply a word `v 0, ..., v (n-1)` of operators to `m`.

Our convention is that `v (n-1)` acts first and `v 0` acts last. -/
def wordApply {T : Type u₁} {M : Type u₂} (act : T → M → M) :
    (n : ℕ) → (Fin n → T) → M → M
  | 0, _, m => m
  | n + 1, v, m => act (v 0) (wordApply act n (fun i => v i.succ) m)

/-- Every word of length `n` in the operators `act v` acts by zero. -/
def IsWordNilpotent {T : Type u₁} {M : Type u₂} [Zero M]
    (n : ℕ) (act : T → M → M) : Prop :=
  ∀ (v : Fin n → T) (m : M), wordApply act n v m = 0

/-- Data recording the restricted `p`-power of tangent derivations.

For a smooth algebra in characteristic `p`, the `p`-fold iterate of a
derivation is again a derivation.  Mathlib currently has no bundled
restricted Lie--Rinehart structure for this fact, so we record the resulting
derivation and its defining evaluation equality explicitly. -/
structure RestrictedPower (k : Type u₁) (A : Type u₂) (p : ℕ)
    [CommRing k] [CommRing A] [Algebra k A]
    [CharP k p] [CharP A p] [Fact p.Prime] where
  pPow : Tangent k A → Tangent k A
  pPow_apply (D : Tangent k A) (a : A) :
    pPow D a = ((D : A → A)^[p]) a

section Higgs

variable (k : Type u₁) (A : Type u₂) (M : Type u₃) (p : ℕ)
variable [CommRing k] [CommRing A] [Algebra k A]
variable [AddCommGroup M] [Module A M]
variable [CharP k p] [CharP A p] [Fact p.Prime]

/-- An integrable Higgs module on the affine chart `Spec A`, nilpotent of
level at most `p - 1`.

The map `theta D` is contraction of the Higgs field with the tangent vector
`D`.  `integrable` is `theta ∧ theta = 0`; it makes all contractions commute.
The last field states the LSZ nilpotence condition: arbitrary `p` tangent
vectors act with zero composite. -/
structure NilpotentHiggs where
  theta : Tangent k A →ₗ[A] Module.End A M
  integrable (D E : Tangent k A) (m : M) :
    theta D (theta E m) = theta E (theta D m)
  nilpotent : IsWordNilpotent p (fun D m => theta D m)

end Higgs

section Connection

variable (k : Type u₁) (A : Type u₂) (M : Type u₃) (p : ℕ)
variable [CommRing k] [CommRing A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M]
variable [IsScalarTower k A M]
variable [CharP k p] [CharP A p] [Fact p.Prime]

/-- An integrable connection on the affine `k`-algebra `A`.

The connection is `A`-linear in its tangent-vector argument and `k`-linear
in the module argument.  The `leibniz` field is the connection Leibniz rule,
and `flat` is vanishing ordinary curvature. -/
structure IntegrableConnection where
  nabla : Tangent k A →ₗ[A] Module.End k M
  leibniz (D : Tangent k A) (a : A) (m : M) :
    nabla D (a • m) = a • nabla D m + D a • m
  flat (D E : Tangent k A) (m : M) :
    nabla ⁅D, E⁆ m = nabla D (nabla E m) - nabla E (nabla D m)

/-- The `p`-curvature as a `k`-linear endomorphism:
`psi(D) = nabla(D)^p - nabla(D^[p])`.

Its `A`-linearity is a theorem following from characteristic `p` and
integrability; it is intentionally not included as extra object data. -/
def pCurvatureKLinear (rp : RestrictedPower k A p)
    (C : IntegrableConnection k A M) (D : Tangent k A) : Module.End k M :=
  C.nabla D ^ p - C.nabla (rp.pPow D)

/-- An integrable flat module whose `p`-curvature is nilpotent of level at
most `p - 1`: every product of `p` possibly different `p`-curvature
contractions is zero. -/
structure NilpotentFlat (rp : RestrictedPower k A p) where
  connection : IntegrableConnection k A M
  nilpotentPCurvature :
    IsWordNilpotent p (fun D m => pCurvatureKLinear k A M p rp connection D m)

end Connection

end LSZ
