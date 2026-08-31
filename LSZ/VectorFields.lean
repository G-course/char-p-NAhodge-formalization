import LSZ.Geometry
import Mathlib.RingTheory.Derivation.Lie

/-!
# Canonical relative vector fields

A vector field on an open `U` is defined here as a compatible family of
`k`-derivations on every smaller open.  This is the elementary, explicit
realization of the sheaf `Der_k(𝒪_X, 𝒪_X)`; it is constructed from the
structure sheaf and contains no user-supplied tangent data.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- The canonical `k`-algebra structure on functions over an open of `X`. -/
@[instance_reducible]
def sectionAlgebra (U : X.scheme.Opens) : Algebra k Γ(X.scheme, U) :=
  X.baseToStructureSheaf.app (.op U) |>.hom.toAlgebra

instance sectionAlgebraInstance (U : X.scheme.Opens) :
    Algebra k Γ(X.scheme, U) := X.sectionAlgebra U

/-- A relative vector field on `U`, expressed as derivations on all smaller
opens which commute with restriction of functions. -/
@[ext]
structure VectorField (U : X.scheme.Opens) where
  deriv (V : X.scheme.Opens) (hV : V ≤ U) :
    Derivation k Γ(X.scheme, V) Γ(X.scheme, V)
  compatible {V W : X.scheme.Opens} (hV : V ≤ U) (hWV : W ≤ V)
      (a : Γ(X.scheme, V)) :
    X.scheme.presheaf.map (homOfLE hWV).op (deriv V hV a) =
      deriv W (hWV.trans hV)
        (X.scheme.presheaf.map (homOfLE hWV).op a)

namespace VectorField

variable {X} {U V W : X.scheme.Opens}

/-- Restriction of a vector field to a smaller open. -/
def restrict (D : X.VectorField U) (hVU : V ≤ U) : X.VectorField V where
  deriv W hW := D.deriv W (hW.trans hVU)
  compatible hW hZW a := D.compatible (hW.trans hVU) hZW a

@[simp]
lemma restrict_deriv (D : X.VectorField U) (hVU : V ≤ U)
    (W : X.scheme.Opens) (hWV : W ≤ V) :
    (D.restrict hVU).deriv W hWV = D.deriv W (hWV.trans hVU) := rfl

/-- Evaluation of a vector field on functions over its ambient open. -/
abbrev act (D : X.VectorField U) : Derivation k Γ(X.scheme, U) Γ(X.scheme, U) :=
  D.deriv U le_rfl

instance : Zero (X.VectorField U) where
  zero :=
    { deriv := fun _ _ => 0
      compatible := by simp }

@[simp]
lemma zero_deriv (V : X.scheme.Opens) (hV : V ≤ U) :
    (0 : X.VectorField U).deriv V hV = 0 := rfl

instance : Add (X.VectorField U) where
  add D E :=
    { deriv := fun V hV => D.deriv V hV + E.deriv V hV
      compatible := by
        intro V W hV hWV a
        simp only [Derivation.add_apply, map_add]
        rw [D.compatible hV hWV a, E.compatible hV hWV a] }

@[simp]
lemma add_deriv (D E : X.VectorField U) (V : X.scheme.Opens) (hV : V ≤ U) :
    (D + E).deriv V hV = D.deriv V hV + E.deriv V hV := rfl

instance : Neg (X.VectorField U) where
  neg D :=
    { deriv := fun V hV => -D.deriv V hV
      compatible := by
        intro V W hV hWV a
        simp only [Derivation.neg_apply, map_neg]
        rw [D.compatible hV hWV a] }

@[simp]
lemma neg_deriv (D : X.VectorField U) (V : X.scheme.Opens) (hV : V ≤ U) :
    (-D).deriv V hV = -D.deriv V hV := rfl

instance : AddCommGroup (X.VectorField U) where
  add_assoc D E F := by ext V hV a; simp [add_assoc]
  zero_add D := by ext V hV a; simp
  add_zero D := by ext V hV a; simp
  nsmul := nsmulRec
  neg_add_cancel D := by ext V hV a; simp
  zsmul := zsmulRec
  add_comm D E := by ext V hV a; simp [add_comm]

/-- Multiplication of a vector field by a function on its ambient open. -/
instance : SMul Γ(X.scheme, U) (X.VectorField U) where
  smul a D :=
    { deriv := fun V hV =>
        (X.scheme.presheaf.map (homOfLE hV).op a) • D.deriv V hV
      compatible := by
        intro V W hV hWV b
        simp only [Derivation.smul_apply, smul_eq_mul, map_mul]
        rw [D.compatible hV hWV b]
        congr 1
        change
          X.scheme.presheaf.map (homOfLE hWV).op
              (X.scheme.presheaf.map (homOfLE hV).op a) =
            X.scheme.presheaf.map (homOfLE (hWV.trans hV)).op a
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl }

@[simp]
lemma smul_deriv (a : Γ(X.scheme, U)) (D : X.VectorField U)
    (V : X.scheme.Opens) (hV : V ≤ U) :
    (a • D).deriv V hV =
      (X.scheme.presheaf.map (homOfLE hV).op a) • D.deriv V hV := rfl

instance : Module Γ(X.scheme, U) (X.VectorField U) where
  one_smul D := by ext V hV a; simp
  mul_smul a b D := by ext V hV c; simp [mul_smul]
  smul_zero a := by ext V hV b; simp
  smul_add a D E := by ext V hV b; simp [smul_add]
  add_smul a b D := by ext V hV c; simp [add_smul]
  zero_smul D := by ext V hV a; simp

/-- The pointwise Lie bracket of canonical vector fields. -/
instance : Bracket (X.VectorField U) (X.VectorField U) where
  bracket D E :=
    { deriv := fun V hV => ⁅D.deriv V hV, E.deriv V hV⁆
      compatible := by
        intro V W hV hWV a
        simp only [Derivation.commutator_apply, map_sub]
        rw [D.compatible hV hWV (E.deriv V hV a),
          E.compatible hV hWV (D.deriv V hV a),
          E.compatible hV hWV a, D.compatible hV hWV a] }

@[simp]
lemma bracket_deriv (D E : X.VectorField U) (V : X.scheme.Opens) (hV : V ≤ U) :
    ⁅D, E⁆.deriv V hV = ⁅D.deriv V hV, E.deriv V hV⁆ := rfl

end VectorField

end

end LSZ.SmoothScheme
