import LSZ.AffineLSZ
import LSZ.GlobalFunctor

/-!
# Comparison of the affine and scheme LSZ formulas

The scheme construction is the one attached to a global Frobenius lift and
its divided differential.  On an affine open, the comparison below assumes
only that the three primitive constructions agree: the canonical
connection, the pulled-back Higgs action, and `d F̃ / p`.  It then proves
that the resulting LSZ connections agree.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

noncomputable section

namespace FixedFrobeniusLift

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {X : AlgebraicGeometry.Scheme.{u}}
variable {L : W₂Lift (p := p) (k := k) X}

/-- The already verified scheme-level LSZ functor, named here alongside the
affine construction.  Its divided differential is the datum canonically
expected from the selected Frobenius lift. -/
noncomputable def schemeFunctor
    (Phi : LSZ.GlobalFrobeniusLift X L)
    (T : RestrictedTangentSheaf X p)
    (D : Phi.DividedDifferentialData T) :
    SchemeObject.IntegrableHiggs T ⥤ SchemeObject.IntegrableConnection T :=
  Phi.globalLSZFunctor T D

@[simp]
lemma schemeFunctor_obj
    (Phi : LSZ.GlobalFrobeniusLift X L)
    (T : RestrictedTangentSheaf X p)
    (D : Phi.DividedDifferentialData T)
    (E : SchemeObject.IntegrableHiggs T) :
    (schemeFunctor Phi T D).obj E = D.connection E := rfl

end FixedFrobeniusLift

namespace AffineSchemeComparison

open Global SchemeObject

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {X : AlgebraicGeometry.Scheme.{u}}
variable {T : RestrictedTangentSheaf X p} {F : X ⟶ X}
variable (Dg : GlobalDividedFrobeniusData T F)
variable (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
variable [Algebra k Γ(X, U)]

/-- Sections of the coefficient sheaf, bundled once so that all subsequent
constructions use the same module instances definitionally. -/
abbrev sectionModule : ModuleCat.{u} Γ(X, U) :=
  ModuleCat.of Γ(X, U) Γ(E.carrier, U)

/-- The affine Higgs module obtained from the sections on `U` and an
identification of algebraic tangent vectors with tangent-sheaf sections. -/
def affineHiggsOf
    (tangentIso : Tangent k Γ(X, U) ≃ₗ[Γ(X, U)] Γ(T.tangent, U)) :
    AffineObject.IntegrableHiggs k Γ(X, U) where
  carrier := sectionModule E U
  theta := (E.theta U).comp tangentIso.toLinearMap
  integrable v w m := E.integrable U (tangentIso v) (tangentIso w) m

/-- Data identifying the three primitive scheme constructions with their
affine counterparts on one affine open.  The final LSZ connection is not a
field: its compatibility is the theorem below. -/
structure Data where
  tangentIso :
    Tangent k Γ(X, U) ≃ₗ[Γ(X, U)] Γ(T.tangent, U)
  pulledTangentIso :
    AffineFrobeniusLift.pullback k Γ(X, U) p
        (AffineFrobeniusLift.tangentModule k Γ(X, U)) ≃ₗ[Γ(X, U)]
      Γ(frobeniusPullback F T.tangent, U)
  carrierIso :
    AffineFrobeniusLift.pullback k Γ(X, U) p
        (affineHiggsOf E U tangentIso).carrier ≃ₗ[Γ(X, U)]
      Γ(pulledBackCarrier F E, U)

/-- The affine Higgs module belonging to comparison data. -/
abbrev Data.affineHiggs (C : Data (k := k) (F := F) E U) :=
  affineHiggsOf E U C.tangentIso

/-- Compatibility hypotheses for the three primitive constructions. -/
structure Compatible (C : Data (k := k) (F := F) E U)
    (Z : AffineFrobeniusLift.DividedDifferential k Γ(X, U) p) : Prop where
  canonical (v : Tangent k Γ(X, U))
      (x : AffineFrobeniusLift.pullback k Γ(X, U) p
        C.affineHiggs.carrier) :
    C.carrierIso
        (StandardFrobeniusPullback.canonicalNabla
          k Γ(X, U) C.affineHiggs.carrier p v x) =
      Dg.canonicalNabla E U (C.tangentIso v) (C.carrierIso x)
  dividedDifferential (v : Tangent k Γ(X, U)) :
    C.pulledTangentIso (AffineFrobeniusLift.DividedDifferential.zeta Z v) =
      Dg.zeta U (C.tangentIso v)
  higgsAction
      (q : AffineFrobeniusLift.pullback k Γ(X, U) p
        (AffineFrobeniusLift.tangentModule k Γ(X, U)))
      (x : AffineFrobeniusLift.pullback k Γ(X, U) p
        C.affineHiggs.carrier) :
    C.carrierIso
        (AffineFrobeniusLift.pullbackTheta
          k Γ(X, U) p C.affineHiggs q x) =
      Dg.pullbackTheta E U (C.pulledTangentIso q) (C.carrierIso x)

/-- The objectwise comparison map, constructed before proving it is
horizontal. -/
def comparisonLinearEquiv (C : Data (k := k) (F := F) E U) :
    AffineFrobeniusLift.pullback k Γ(X, U) p
        C.affineHiggs.carrier ≃ₗ[Γ(X, U)]
      Γ(pulledBackCarrier F E, U) :=
  C.carrierIso

/-- On an affine open, the scheme LSZ connection is the affine LSZ
connection after the standard identifications. -/
theorem comparison_nabla
    (C : Data (k := k) (F := F) E U)
    (Z : AffineFrobeniusLift.DividedDifferential k Γ(X, U) p)
    (h : Compatible Dg E U C Z)
    (v : Tangent k Γ(X, U))
    (x : AffineFrobeniusLift.pullback k Γ(X, U) p
      C.affineHiggs.carrier) :
    comparisonLinearEquiv E U C
        (AffineFrobeniusLift.DividedDifferential.nabla
          k Γ(X, U) p Z C.affineHiggs v x) =
      Dg.nabla E U (C.tangentIso v)
        (comparisonLinearEquiv E U C x) := by
  change C.carrierIso
      (AffineFrobeniusLift.DividedDifferential.nabla
        k Γ(X, U) p Z C.affineHiggs v x) =
    Dg.nabla E U (C.tangentIso v) (C.carrierIso x)
  rw [AffineFrobeniusLift.DividedDifferential.nabla_apply]
  rw [map_add, h.canonical,
    h.higgsAction, h.dividedDifferential,
    GlobalDividedFrobeniusData.nabla_apply,
    GlobalCartierData.correction_apply]

end AffineSchemeComparison

end


end LSZ
