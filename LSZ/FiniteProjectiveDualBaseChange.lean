import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Duals of finite projective modules and base change

Mathlib supplies the canonical base-change equivalence for finite free
modules.  This file extends the result to finite projective modules by
exhibiting such a module as a retract of a finite free module.
-/

open TensorProduct
open scoped ChangeOfRings

namespace LSZ

noncomputable section

namespace FiniteProjectiveDualBaseChange

universe u v w x

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Identify mathlib's bundled extension-of-scalars object with the
unbundled algebra tensor product. -/
def extensionTensorEquiv :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) ≃ₗ[S]
      S ⊗[R] M := by
  let L := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : IsScalarTower R S L :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eL : L ≃ₗ[S] S := LinearEquiv.refl S S
  exact AlgebraTensorModule.congr eL (LinearEquiv.refl R M)

@[simp]
lemma extensionTensorEquiv_tmul (s : S) (m : M) :
    extensionTensorEquiv (R := R) (S := S) (M := M)
        (s ⊗ₜ[R, algebraMap R S] m) =
      s ⊗ₜ[R] m := rfl

/-- The canonical map from the base change of the dual to the dual of the
base change. -/
def hom : S ⊗[R] Module.Dual R M →ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.Dual.baseChange S :
    Module.Dual R M →ₗ[R] Module.Dual S (S ⊗[R] M)).liftBaseChange S

@[simp]
lemma hom_tmul_apply (s t : S) (phi : Module.Dual R M) (m : M) :
    hom (R := R) (S := S) (M := M) (s ⊗ₜ[R] phi) (t ⊗ₜ[R] m) =
      s * (algebraMap R S (phi m) * t) := by
  rw [hom, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, smul_eq_mul, Algebra.smul_def]

variable {N : Type x} [AddCommGroup N] [Module R N]

/-- Naturality of the canonical dual base-change map. -/
lemma hom_naturality (f : M →ₗ[R] N) :
    (LinearMap.baseChange S f).dualMap.comp
        (hom (R := R) (S := S) (M := N)) =
      (hom (R := R) (S := S) (M := M)).comp
        (LinearMap.baseChange S f.dualMap) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s phi =>
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy =>
          simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy
      | tmul t m =>
          rw [LinearMap.comp_apply, LinearMap.dualMap_apply,
            LinearMap.baseChange_tmul, hom_tmul_apply,
            LinearMap.comp_apply, LinearMap.baseChange_tmul,
            hom_tmul_apply, LinearMap.dualMap_apply]

private noncomputable def freeEquiv (n : ℕ) :
    S ⊗[R] Module.Dual R (Fin n → R) ≃ₗ[S]
      Module.Dual S (S ⊗[R] (Fin n → R)) :=
  IsBaseChange.toDualBaseChange
    (TensorProduct.isBaseChange R (Fin n → R) S)

private lemma freeEquiv_apply_eq_hom (n : ℕ)
    (z : S ⊗[R] Module.Dual R (Fin n → R)) :
    freeEquiv (R := R) (S := S) n z =
      hom (R := R) (S := S) (M := Fin n → R) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s phi =>
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul t m =>
          have h := IsBaseChange.toDualBaseChange_tmul
            (TensorProduct.isBaseChange R (Fin n → R) S) s phi m
          have htm : (t ⊗ₜ[R] m : S ⊗[R] (Fin n → R)) =
              t • ((1 : S) ⊗ₜ[R] m) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [htm]
          rw [LinearMap.map_smul, LinearMap.map_smul]
          apply congrArg (fun x : S ↦ t • x)
          change (freeEquiv (R := R) (S := S) n (s ⊗ₜ[R] phi))
              ((TensorProduct.mk R S (Fin n → R) 1) m) =
            (hom (R := R) (S := S) (M := Fin n → R)
              (s ⊗ₜ[R] phi)) ((1 : S) ⊗ₜ[R] m)
          calc
            _ = s * algebraMap R S (phi m) := h
            _ = _ := by rw [hom_tmul_apply, mul_one]

/-- For a finite projective module, the canonical dual base-change map is
bijective. -/
theorem hom_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (hom (R := R) (S := S) (M := M)) := by
  obtain ⟨n, f, g, -, -, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  let e := freeEquiv (R := R) (S := S) n
  let inverse : Module.Dual S (S ⊗[R] M) →ₗ[S]
      S ⊗[R] Module.Dual R M :=
    (LinearMap.baseChange S g.dualMap).comp
      (e.symm.toLinearMap.comp (LinearMap.baseChange S f).dualMap)
  have hdual : g.dualMap.comp f.dualMap = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, hfg, LinearMap.dualMap_id]
  have hbaseDual :
      (LinearMap.baseChange S g.dualMap).comp
          (LinearMap.baseChange S f.dualMap) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hdual, LinearMap.baseChange_id]
  have hbase :
      (LinearMap.baseChange S g).dualMap.comp
          (LinearMap.baseChange S f).dualMap = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap,
      ← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id,
      LinearMap.dualMap_id]
  have hinverse_left (z : S ⊗[R] Module.Dual R M) :
      inverse (hom (R := R) (S := S) (M := M) z) = z := by
    have hf := LinearMap.congr_fun (hom_naturality (R := R) (S := S) f) z
    change (LinearMap.baseChange S f).dualMap
        (hom (R := R) (S := S) (M := M) z) =
      hom (R := R) (S := S) (M := Fin n → R)
        (LinearMap.baseChange S f.dualMap z) at hf
    change (LinearMap.baseChange S g.dualMap)
      (e.symm ((LinearMap.baseChange S f).dualMap
        (hom (R := R) (S := S) (M := M) z))) = z
    rw [hf]
    have he : e.symm
        (hom (R := R) (S := S) (M := Fin n → R)
          (LinearMap.baseChange S f.dualMap z)) =
        LinearMap.baseChange S f.dualMap z := by
      rw [← freeEquiv_apply_eq_hom]
      exact e.symm_apply_apply _
    rw [he]
    exact LinearMap.congr_fun hbaseDual z
  have hinverse_right (z : Module.Dual S (S ⊗[R] M)) :
      hom (R := R) (S := S) (M := M) (inverse z) = z := by
    let q := e.symm ((LinearMap.baseChange S f).dualMap z)
    have hg := LinearMap.congr_fun
      (hom_naturality (R := R) (S := S) g) q
    change (LinearMap.baseChange S g).dualMap
        (hom (R := R) (S := S) (M := Fin n → R) q) =
      hom (R := R) (S := S) (M := M)
        (LinearMap.baseChange S g.dualMap q) at hg
    change hom (R := R) (S := S) (M := M)
      (LinearMap.baseChange S g.dualMap q) = z
    rw [← hg]
    have he : hom (R := R) (S := S) (M := Fin n → R) q =
        (LinearMap.baseChange S f).dualMap z := by
      rw [← freeEquiv_apply_eq_hom]
      exact e.apply_symm_apply _
    rw [he]
    exact LinearMap.congr_fun hbase z
  constructor
  · intro x y hxy
    rw [← hinverse_left x, hxy, hinverse_left y]
  · intro y
    exact ⟨inverse y, hinverse_right y⟩

/-- Duals of finite projective modules commute with arbitrary base change. -/
def equiv [Module.Finite R M] [Module.Projective R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (hom (R := R) (S := S) (M := M)) hom_bijective

@[simp]
lemma equiv_apply [Module.Finite R M] [Module.Projective R M]
    (z : S ⊗[R] Module.Dual R M) :
    equiv (R := R) (S := S) (M := M) z =
      hom (R := R) (S := S) (M := M) z := rfl

end FiniteProjectiveDualBaseChange

end

end LSZ
