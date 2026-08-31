import LSZ.InverseImageTensor

/-!
# Explicit pullback of module presheaves and tensor products

For a continuous map `f : X ⟶ Y`, a commutative-ring presheaf `A` on `Y`,
a commutative-ring presheaf `B` on `X`, and a map `f⁻¹A ⟶ B`, the explicit
pullback is the composite of inverse image and objectwise extension of
scalars.  This file proves that this composite preserves tensor products.
-/

open CategoryTheory TopologicalSpace
open scoped MonoidalCategory

namespace LSZ.PullbackPresheafTensor

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (A : Y.Presheaf CommRingCat.{u})
  (B : X.Presheaf CommRingCat.{u})
  (alpha : InverseImagePresheaf.ring f A ⟶ B)

/-- Explicit pullback of module presheaves: inverse image followed by
extension of scalars. -/
noncomputable def functor :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  InverseImagePresheaf.moduleFunctor f A ⋙
    CommRingSheaf.extensionPresheafFunctor alpha

private noncomputable abbrev sourceTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)))

private noncomputable abbrev targetTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)))

/-- First tensor, then apply the explicit pullback. -/
noncomputable def tensorSourceFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  sourceTensorBifunctor (A := A) ⋙ functor f A B alpha

/-- Apply the explicit pullback to both factors, then tensor. -/
noncomputable def tensorTargetFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  Functor.prod (functor f A B alpha) (functor f A B alpha) ⋙
    targetTensorBifunctor B

/-- The tensor comparison for two individual module presheaves.  The two
constituent isomorphisms are kept visible: inverse image first, then extension
of scalars. -/
noncomputable def tensorObjIso
    (M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    (functor f A B alpha).obj (M ⊗ N) ≅
      (functor f A B alpha).obj M ⊗ (functor f A B alpha).obj N :=
  (CommRingSheaf.extensionPresheafFunctor alpha).mapIso
      (InverseImageTensor.inverseImageTensorIso f A M N) ≪≫
    CommRingSheaf.extensionTensorPresheafIso alpha
      ((InverseImagePresheaf.moduleFunctor f A).obj M)
      ((InverseImagePresheaf.moduleFunctor f A).obj N)

private noncomputable def inverseImageComparisonNatIso :
    InverseImageTensor.inverseImageTensorSourceFunctor f A ⋙
        CommRingSheaf.extensionPresheafFunctor alpha ≅
      InverseImageTensor.inverseImageTensorTargetFunctor f A ⋙
        CommRingSheaf.extensionPresheafFunctor alpha :=
  Functor.isoWhiskerRight (InverseImageTensor.inverseImageTensorNatIso f A)
    (CommRingSheaf.extensionPresheafFunctor alpha)

private noncomputable def extensionComparisonNatIso :
    Functor.prod (InverseImagePresheaf.moduleFunctor f A)
          (InverseImagePresheaf.moduleFunctor f A) ⋙
        CommRingSheaf.extensionTensorSourceFunctor alpha ≅
      Functor.prod (InverseImagePresheaf.moduleFunctor f A)
          (InverseImagePresheaf.moduleFunctor f A) ⋙
        CommRingSheaf.extensionTensorTargetFunctor alpha :=
  Functor.isoWhiskerLeft
    (Functor.prod (InverseImagePresheaf.moduleFunctor f A)
      (InverseImagePresheaf.moduleFunctor f A))
    (CommRingSheaf.extensionTensorPresheafNatIso alpha)

private noncomputable def tensorNatIsoCore :
    tensorSourceFunctor f A B alpha ≅ tensorTargetFunctor f A B alpha :=
  inverseImageComparisonNatIso f A B alpha ≪≫
    extensionComparisonNatIso f A B alpha

private lemma tensorObjIso_eq_core_app
    (M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    tensorObjIso f A B alpha M N =
      (tensorNatIsoCore f A B alpha).app (M, N) := by
  rfl

private lemma tensorObjIso_naturality
    {MN PQ :
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
        PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : MN ⟶ PQ) :
    (tensorSourceFunctor f A B alpha).map g ≫
        (tensorObjIso f A B alpha PQ.1 PQ.2).hom =
      (tensorObjIso f A B alpha MN.1 MN.2).hom ≫
        (tensorTargetFunctor f A B alpha).map g := by
  rw [tensorObjIso_eq_core_app, tensorObjIso_eq_core_app]
  exact (tensorNatIsoCore f A B alpha).hom.naturality g

/-- Explicit pullback of module presheaves preserves tensor products,
naturally in both module presheaves. -/
noncomputable def tensorNatIso :
    tensorSourceFunctor f A B alpha ≅ tensorTargetFunctor f A B alpha :=
  NatIso.ofComponents
    (fun MN ↦ tensorObjIso f A B alpha MN.1 MN.2)
    (tensorObjIso_naturality f A B alpha)

end

end LSZ.PullbackPresheafTensor
