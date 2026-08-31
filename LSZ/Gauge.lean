import LSZ.CoverFunctor
import LSZ.TruncatedExp

/-!
# Exponential gauges for LSZ descent

This file upgrades the sectionwise truncated exponential to an isomorphism
of sheaves of modules.  The sheaf morphisms are part of the descent output;
their application formulas are required to be the actual finite sums.  The
inverse equations are then proved, not assumed.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ}

namespace Gauge

open SchemeObject

/-- A morphism of sheaves of modules evaluated on an open set, bundled as
a linear map over the ring of functions on that open set. -/
noncomputable def appLinear {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := fun m ↦ (f.val.app (.op U)).hom m
  map_add' := (f.val.app (.op U)).hom.map_add
  map_smul' := (f.val.app (.op U)).hom.map_smul

@[simp]
lemma appLinear_apply {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (m : Γ(M, U)) :
    appLinear f U m = f.app U m := rfl

@[simp]
lemma appLinear_add {M N : X.Modules} (f g : M ⟶ N) (U : X.Opens) :
    appLinear (f + g) U = appLinear f U + appLinear g U := rfl

variable (T : RestrictedTangentSheaf X p) (M : X.Modules)
variable [Fact p.Prime]

/-- A sheaf endomorphism together with the two sheaf morphisms represented
sectionwise by `exp_p(a)` and `exp_p(-a)`.

The mixed nilpotence assumptions are the direct algebraic consequences of
the LSZ condition that every word of length `p` in Higgs contractions is
zero. -/
structure Exponential where
  exponent : M ⟶ M
  expHom : M ⟶ M
  expNegHom : M ⟶ M
  positive_negative_nilpotent (U : X.Opens) :
    ∀ i j : ℕ, p ≤ i + j →
      (appLinear exponent U) ^ i * (-(appLinear exponent U)) ^ j = 0
  negative_positive_nilpotent (U : X.Opens) :
    ∀ i j : ℕ, p ≤ i + j →
      (-(appLinear exponent U)) ^ i * (appLinear exponent U) ^ j = 0
  expHom_app (U : X.Opens) (m : Γ(M, U)) :
    expHom.app U m =
      TruncatedExp.moduleEndExpOf p (T.characteristic U)
        (appLinear exponent U) m
  expNegHom_app (U : X.Opens) (m : Γ(M, U)) :
    expNegHom.app U m =
      TruncatedExp.moduleEndExpOf p (T.characteristic U)
        (-(appLinear exponent U)) m

namespace Exponential

variable {T : RestrictedTangentSheaf X p} {M : X.Modules}

lemma hom_inv_id (G : Exponential T M) :
    G.expHom ≫ G.expNegHom = 𝟙 M := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext m
  change G.expNegHom.app U (G.expHom.app U m) = m
  rw [G.expHom_app, G.expNegHom_app]
  letI : CharP Γ(X, U) p := T.characteristic U
  have h := TruncatedExp.moduleEndExp_neg_mul_eq_one p
    (G.negative_positive_nilpotent U)
  have hm := congrArg (fun f : Module.End Γ(X, U) Γ(M, U) ↦ f m) h
  exact hm

lemma inv_hom_id (G : Exponential T M) :
    G.expNegHom ≫ G.expHom = 𝟙 M := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext m
  change G.expHom.app U (G.expNegHom.app U m) = m
  rw [G.expNegHom_app, G.expHom_app]
  letI : CharP Γ(X, U) p := T.characteristic U
  have h := TruncatedExp.moduleEndExp_mul_neg_eq_one p
    (G.positive_negative_nilpotent U)
  have hm := congrArg (fun f : Module.End Γ(X, U) Γ(M, U) ↦ f m) h
  exact hm

/-- The LSZ truncated exponential as an isomorphism of sheaves of
modules.  Invertibility is a theorem from length-`p` nilpotence. -/
noncomputable def iso (G : Exponential T M) : M ≅ M where
  hom := G.expHom
  inv := G.expNegHom
  hom_inv_id := G.hom_inv_id
  inv_hom_id := G.inv_hom_id

@[simp]
lemma iso_hom (G : Exponential T M) : G.iso.hom = G.expHom := rfl

@[simp]
lemma iso_inv (G : Exponential T M) : G.iso.inv = G.expNegHom := rfl

/-- The additive divided-difference identity on a triple overlap.  In LSZ
notation this is `h₀₂ = h₀₁ + h₁₂`; the remaining fields are precisely the
commutation and total-degree-`p` vanishing needed by the truncated
exponential addition theorem. -/
structure AdditiveCocycle
    (G₀₁ G₁₂ G₀₂ : Exponential T M) : Prop where
  exponent_add : G₀₂.exponent = G₀₁.exponent + G₁₂.exponent
  commute (U : X.Opens) :
    Commute (appLinear G₀₁.exponent U) (appLinear G₁₂.exponent U)
  joint_nilpotent (U : X.Opens) :
    ∀ i j : ℕ, p ≤ i + j →
      (appLinear G₀₁.exponent U) ^ i *
        (appLinear G₁₂.exponent U) ^ j = 0

/-- The exponential transition maps satisfy the cocycle equation.  The
categorical order says: first apply `G₁₂`, then apply `G₀₁`. -/
lemma AdditiveCocycle.expHom_cocycle
    {G₀₁ G₁₂ G₀₂ : Exponential T M}
    (C : AdditiveCocycle G₀₁ G₁₂ G₀₂) :
    G₁₂.expHom ≫ G₀₁.expHom = G₀₂.expHom := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext m
  change G₀₁.expHom.app U (G₁₂.expHom.app U m) = G₀₂.expHom.app U m
  rw [G₀₁.expHom_app, G₁₂.expHom_app, G₀₂.expHom_app]
  letI : CharP Γ(X, U) p := T.characteristic U
  have hadd : appLinear G₀₂.exponent U =
      appLinear G₀₁.exponent U + appLinear G₁₂.exponent U := by
    rw [C.exponent_add, appLinear_add]
  rw [hadd]
  change
    TruncatedExp.moduleEndExp p (appLinear G₀₁.exponent U)
        (TruncatedExp.moduleEndExp p (appLinear G₁₂.exponent U) m) =
      TruncatedExp.moduleEndExp p
        (appLinear G₀₁.exponent U + appLinear G₁₂.exponent U) m
  have h := TruncatedExp.moduleEndExp_add_of_commute_of_jointNilpotent p
    (C.commute U) (C.joint_nilpotent U)
  have hm := congrArg (fun f : Module.End Γ(X, U) Γ(M, U) ↦ f m) h
  exact hm.symm

end Exponential

end Gauge

end LSZ
