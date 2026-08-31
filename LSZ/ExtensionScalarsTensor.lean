import LSZ.ExtensionScalars
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extension of scalars and tensor products

The comparison is the ring-theoretic base-change isomorphism
`B ⊗[A] (M ⊗[A] N) ≅ (B ⊗[A] M) ⊗[B] (B ⊗[A] N)`.
The presheaf statements below only package this objectwise construction and
verify its compatibility with restriction maps.
-/

open CategoryTheory Opposite
open scoped MonoidalCategory TensorProduct ChangeOfRings

set_option maxHeartbeats 1000000

namespace LSZ.CommRingSheaf

universe u v₁ u₁

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
  {A B : Functor Cᵒᵖ CommRingCat.{u}} (alpha : A ⟶ B)
  (M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))

noncomputable local instance sourcePresheafModulesMonoidal :
    MonoidalCategory
      (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :=
  inferInstance

noncomputable local instance targetPresheafModulesMonoidal :
    MonoidalCategory
      (PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)) :=
  inferInstance

private noncomputable abbrev extensionTensorSectionSource (U : Cᵒᵖ) :
    ModuleCat (B.obj U) :=
  (extensionPresheaf alpha (M ⊗ N)).obj U

private noncomputable abbrev extensionTensorSectionTarget (U : Cᵒᵖ) :
    ModuleCat (B.obj U) :=
  (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).obj U

/-- The concrete base-change isomorphism on one object of the site. -/
noncomputable def extensionTensorSectionIso (U : Cᵒᵖ) :
    extensionTensorSectionSource alpha M N U ≅
      extensionTensorSectionTarget alpha M N U := by
  letI : Algebra (A.obj U) (B.obj U) := (alpha.app U).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange
    (A.obj U) (B.obj U) (M.obj U) (N.obj U)).toModuleIso

@[simp]
lemma extensionTensorSectionIso_hom_unit_tmul
    (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U) :
    (extensionTensorSectionIso alpha M N U).hom
        (extensionUnit alpha (M ⊗ N) U
          (m ⊗ₜ[A.obj U] n)) =
      extensionUnit alpha M U m ⊗ₜ[B.obj U]
        extensionUnit alpha N U n := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma extensionTensorSectionIso_naturality
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (extensionPresheaf alpha (M ⊗ N)).map i ≫
        (ModuleCat.restrictScalars (B.map i).hom).map
          (extensionTensorSectionIso alpha M N V).hom =
      (extensionTensorSectionIso alpha M N U).hom ≫
        (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i := by
  apply extensionHom_ext alpha (M ⊗ N) U
  intro z
  change (extensionTensorSectionIso alpha M N V).hom
      (extensionPresheafMap alpha (M ⊗ N) i
        (extensionUnit alpha (M ⊗ N) U z)) =
    (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
      ((extensionTensorSectionIso alpha M N U).hom
        (extensionUnit alpha (M ⊗ N) U z))
  induction z using TensorProduct.induction_on with
  | zero =>
      have hzero : extensionUnit alpha (M ⊗ N) U 0 = 0 :=
        map_zero ((ModuleCat.extendRestrictScalarsAdj
          (alpha.app U).hom).unit.app ((M ⊗ N).obj U)).hom
      have hsource : extensionPresheafMap alpha (M ⊗ N) i
          (extensionUnit alpha (M ⊗ N) U 0) = 0 := by
        rw [hzero]
        exact map_zero (extensionPresheafMap alpha (M ⊗ N) i).hom
      calc
        _ = (extensionTensorSectionIso alpha M N V).hom 0 :=
          congrArg (extensionTensorSectionIso alpha M N V).hom hsource
        _ = 0 := map_zero (extensionTensorSectionIso alpha M N V).hom.hom
        _ = (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i 0 :=
          (map_zero ((extensionPresheaf alpha M ⊗
            extensionPresheaf alpha N).map i).hom).symm
        _ = (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
            ((extensionTensorSectionIso alpha M N U).hom
              (extensionUnit alpha (M ⊗ N) U 0)) := by
          have hiso : (extensionTensorSectionIso alpha M N U).hom
              (extensionUnit alpha (M ⊗ N) U 0) = 0 := by
            rw [hzero]
            exact map_zero (extensionTensorSectionIso alpha M N U).hom.hom
          exact congrArg (fun x =>
            (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i x) hiso.symm
  | tmul m n =>
      have hmn : mappedSection (M ⊗ N) i (m ⊗ₜ[A.obj U] n) =
          mappedSection M i m ⊗ₜ[A.obj V] mappedSection N i n :=
        PresheafOfModules.Monoidal.tensorObj_map_tmul i m n
      have hsource :
          extensionPresheafMap alpha (M ⊗ N) i
              (extensionUnit alpha (M ⊗ N) U (m ⊗ₜ[A.obj U] n)) =
            extensionUnit alpha (M ⊗ N) V
              (mappedSection M i m ⊗ₜ[A.obj V] mappedSection N i n) :=
        (extensionPresheafMap_unit alpha (M ⊗ N) i
          (m ⊗ₜ[A.obj U] n)).trans
            (congrArg (extensionUnit alpha (M ⊗ N) V) hmn)
      have hV := extensionTensorSectionIso_hom_unit_tmul
        alpha M N V (mappedSection M i m) (mappedSection N i n)
      have hU := extensionTensorSectionIso_hom_unit_tmul alpha M N U m n
      have htensor := PresheafOfModules.Monoidal.tensorObj_map_tmul
        (M₁ := extensionPresheaf alpha M)
        (M₂ := extensionPresheaf alpha N) i
          (extensionUnit alpha M U m) (extensionUnit alpha N U n)
      have hm := extensionPresheafMap_unit alpha M i m
      have hn := extensionPresheafMap_unit alpha N i n
      have htarget :
          (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
              (extensionUnit alpha M U m ⊗ₜ[B.obj U]
                extensionUnit alpha N U n) =
            extensionUnit alpha M V (mappedSection M i m) ⊗ₜ[B.obj V]
              extensionUnit alpha N V (mappedSection N i n) :=
        htensor.trans (congrArg₂
          (fun x y => x ⊗ₜ[B.obj V] y) hm hn)
      calc
        _ = (extensionTensorSectionIso alpha M N V).hom
            (extensionUnit alpha (M ⊗ N) V
              (mappedSection M i m ⊗ₜ[A.obj V] mappedSection N i n)) :=
          congrArg (extensionTensorSectionIso alpha M N V).hom hsource
        _ = extensionUnit alpha M V (mappedSection M i m) ⊗ₜ[B.obj V]
            extensionUnit alpha N V (mappedSection N i n) := hV
        _ = (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
            (extensionUnit alpha M U m ⊗ₜ[B.obj U]
              extensionUnit alpha N U n) := htarget.symm
        _ = (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
            ((extensionTensorSectionIso alpha M N U).hom
              (extensionUnit alpha (M ⊗ N) U (m ⊗ₜ[A.obj U] n))) :=
          congrArg (fun x =>
            (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i x) hU.symm
  | add x y hx hy =>
      have hunit : extensionUnit alpha (M ⊗ N) U (x + y) =
          extensionUnit alpha (M ⊗ N) U x +
            extensionUnit alpha (M ⊗ N) U y :=
        extensionUnit_add alpha (M ⊗ N) U x y
      have hext : extensionPresheafMap alpha (M ⊗ N) i
            (extensionUnit alpha (M ⊗ N) U (x + y)) =
          extensionPresheafMap alpha (M ⊗ N) i
              (extensionUnit alpha (M ⊗ N) U x) +
            extensionPresheafMap alpha (M ⊗ N) i
              (extensionUnit alpha (M ⊗ N) U y) :=
        (congrArg (extensionPresheafMap alpha (M ⊗ N) i) hunit).trans
          (map_add (extensionPresheafMap alpha (M ⊗ N) i).hom _ _)
      have hleft :
          (extensionTensorSectionIso alpha M N V).hom
              (extensionPresheafMap alpha (M ⊗ N) i
                (extensionUnit alpha (M ⊗ N) U (x + y))) =
            (extensionTensorSectionIso alpha M N V).hom
                (extensionPresheafMap alpha (M ⊗ N) i
                  (extensionUnit alpha (M ⊗ N) U x)) +
              (extensionTensorSectionIso alpha M N V).hom
                (extensionPresheafMap alpha (M ⊗ N) i
                  (extensionUnit alpha (M ⊗ N) U y)) :=
        (congrArg (extensionTensorSectionIso alpha M N V).hom hext).trans
          (map_add (extensionTensorSectionIso alpha M N V).hom.hom _ _)
      have hiso :
          (extensionTensorSectionIso alpha M N U).hom
              (extensionUnit alpha (M ⊗ N) U (x + y)) =
            (extensionTensorSectionIso alpha M N U).hom
                (extensionUnit alpha (M ⊗ N) U x) +
              (extensionTensorSectionIso alpha M N U).hom
                (extensionUnit alpha (M ⊗ N) U y) :=
        (congrArg (extensionTensorSectionIso alpha M N U).hom hunit).trans
          (map_add (extensionTensorSectionIso alpha M N U).hom.hom _ _)
      have hright :
          (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
              ((extensionTensorSectionIso alpha M N U).hom
                (extensionUnit alpha (M ⊗ N) U (x + y))) =
            (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
                ((extensionTensorSectionIso alpha M N U).hom
                  (extensionUnit alpha (M ⊗ N) U x)) +
              (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i
                ((extensionTensorSectionIso alpha M N U).hom
                  (extensionUnit alpha (M ⊗ N) U y)) :=
        (congrArg (fun z =>
          (extensionPresheaf alpha M ⊗ extensionPresheaf alpha N).map i z) hiso).trans
          (map_add ((extensionPresheaf alpha M ⊗
            extensionPresheaf alpha N).map i).hom _ _)
      exact hleft.trans ((congrArg₂ (· + ·) hx hy).trans hright.symm)

/-- Objectwise extension of scalars distributes over the presheaf tensor product. -/
noncomputable def extensionTensorPresheafIso :
    extensionPresheaf alpha (M ⊗ N) ≅
      extensionPresheaf alpha M ⊗ extensionPresheaf alpha N :=
  PresheafOfModules.isoMk
    (extensionTensorSectionIso alpha M N)
    (fun {U V} i =>
      extensionTensorSectionIso_naturality alpha M N (U := U) (V := V) i)

set_option backward.isDefEq.respectTransparency false in
lemma extensionTensorPresheafIso_naturality
    {M M' N N' :
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (extensionPresheafFunctor alpha).map (f ⊗ₘ g) ≫
        (extensionTensorPresheafIso alpha M' N').hom =
      (extensionTensorPresheafIso alpha M N).hom ≫
        ((extensionPresheafFunctor alpha).map f ⊗ₘ
          (extensionPresheafFunctor alpha).map g) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply extensionHom_ext alpha (M ⊗ N) U
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      have hzero : extensionUnit alpha (M ⊗ N) U 0 = 0 :=
        map_zero ((ModuleCat.extendRestrictScalarsAdj
          (alpha.app U).hom).unit.app ((M ⊗ N).obj U)).hom
      rw [hzero]
      simp only [map_zero]
  | tmul m n =>
      have hfg := extensionUnit_naturality alpha (f ⊗ₘ g) U
        (m ⊗ₜ[A.obj U] n)
      have htensor :
          (f ⊗ₘ g).app U (m ⊗ₜ[A.obj U] n) =
            f.app U m ⊗ₜ[A.obj U] g.app U n := by
        exact ModuleCat.MonoidalCategory.tensorHom_tmul
          (f.app U) (g.app U) m n
      have hleft :
          (extensionTensorSectionIso alpha M' N' U).hom
              (((extensionPresheafFunctor alpha).map (f ⊗ₘ g)).app U
                (extensionUnit alpha (M ⊗ N) U (m ⊗ₜ[A.obj U] n))) =
            extensionUnit alpha M' U (f.app U m) ⊗ₜ[B.obj U]
              extensionUnit alpha N' U (g.app U n) := by
        change (extensionTensorSectionIso alpha M' N' U).hom
            ((ModuleCat.extendScalars (alpha.app U).hom).map
              ((f ⊗ₘ g).app U)
                (extensionUnit alpha (M ⊗ N) U
                  (m ⊗ₜ[A.obj U] n))) = _
        rw [hfg, htensor]
        exact extensionTensorSectionIso_hom_unit_tmul
          alpha M' N' U (f.app U m) (g.app U n)
      have hright :
          (((extensionPresheafFunctor alpha).map f ⊗ₘ
              (extensionPresheafFunctor alpha).map g).app U)
              (extensionUnit alpha M U m ⊗ₜ[B.obj U]
              extensionUnit alpha N U n) =
            extensionUnit alpha M' U (f.app U m) ⊗ₜ[B.obj U]
              extensionUnit alpha N' U (g.app U n) := by
        change (((ModuleCat.extendScalars (alpha.app U).hom).map (f.app U)) ⊗ₘ
            ((ModuleCat.extendScalars (alpha.app U).hom).map (g.app U)))
              (extensionUnit alpha M U m ⊗ₜ[B.obj U]
                extensionUnit alpha N U n) = _
        rw [ModuleCat.MonoidalCategory.tensorHom_tmul,
          extensionUnit_naturality, extensionUnit_naturality]
      change (extensionTensorSectionIso alpha M' N' U).hom
          (((extensionPresheafFunctor alpha).map (f ⊗ₘ g)).app U
            (extensionUnit alpha (M ⊗ N) U (m ⊗ₜ[A.obj U] n))) =
        (((extensionPresheafFunctor alpha).map f ⊗ₘ
            (extensionPresheafFunctor alpha).map g).app U)
          ((extensionTensorSectionIso alpha M N U).hom
            (extensionUnit alpha (M ⊗ N) U (m ⊗ₜ[A.obj U] n)))
      rw [extensionTensorSectionIso_hom_unit_tmul]
      exact hleft.trans hright.symm
  | add x y hx hy =>
      have hunit : extensionUnit alpha (M ⊗ N) U (x + y) =
          extensionUnit alpha (M ⊗ N) U x +
            extensionUnit alpha (M ⊗ N) U y :=
        extensionUnit_add alpha (M ⊗ N) U x y
      rw [hunit]
      simp only [map_add]
      rw [hx, hy]

private noncomputable abbrev sourceTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)))

private noncomputable abbrev targetTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)))

/-- First tensor, then extend scalars objectwise. -/
noncomputable def extensionTensorSourceFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
        PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  sourceTensorBifunctor (A := A) ⋙ extensionPresheafFunctor alpha

/-- First extend both factors, then tensor. -/
noncomputable def extensionTensorTargetFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
        PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  Functor.prod (extensionPresheafFunctor alpha)
      (extensionPresheafFunctor alpha) ⋙
    targetTensorBifunctor (B := B)

/-- Objectwise extension of scalars distributes naturally over tensor products. -/
noncomputable def extensionTensorPresheafNatIso :
    extensionTensorSourceFunctor alpha ≅
      extensionTensorTargetFunctor alpha :=
  NatIso.ofComponents
    (fun MN => extensionTensorPresheafIso alpha MN.1 MN.2)
    (fun {X Y} f => by
      dsimp [extensionTensorSourceFunctor, extensionTensorTargetFunctor,
        sourceTensorBifunctor, targetTensorBifunctor]
      rw [← MonoidalCategory.tensorHom_def,
        ← MonoidalCategory.tensorHom_def]
      exact extensionTensorPresheafIso_naturality alpha f.1 f.2)


end

end LSZ.CommRingSheaf
