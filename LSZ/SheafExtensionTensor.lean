import LSZ.ExtensionScalarsTensor

/-!
# Sheafified extension of scalars and tensor products

The only comparison used here is the presheaf isomorphism from
`LSZ.ExtensionScalarsTensor`; applying the sheafification functor sends it
to an isomorphism of module sheaves.
-/

open CategoryTheory
open scoped MonoidalCategory

namespace LSZ.CommRingSheaf

universe u v₁ u₁

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (alpha : A ⟶ B)

private noncomputable abbrev sheafifiedExtensionTensorSource
    (M N : Modules A) : Modules B :=
  (directSheafificationFunctor B).obj
    ((extensionTensorSourceFunctor alpha.hom).obj
      ((directForgetFunctor A).obj M, (directForgetFunctor A).obj N))

private noncomputable abbrev sheafifiedExtensionTensorTarget
    (M N : Modules A) : Modules B :=
  (directSheafificationFunctor B).obj
    ((extensionTensorTargetFunctor alpha.hom).obj
      ((directForgetFunctor A).obj M, (directForgetFunctor A).obj N))

/-- Sheafification of the objectwise ring-module base-change isomorphism. -/
noncomputable def sheafifiedExtensionTensorIso (M N : Modules A) :
    sheafifiedExtensionTensorSource alpha M N ≅
      sheafifiedExtensionTensorTarget alpha M N :=
  (directSheafificationFunctor B).mapIso
    ((extensionTensorPresheafNatIso alpha.hom).app
      ((directForgetFunctor A).obj M, (directForgetFunctor A).obj N))

private noncomputable abbrev directForgetPairFunctor :
    Modules A × Modules A ⥤
      PresheafOfModules.{u} (A.obj ⋙ forget₂ CommRingCat RingCat) ×
        PresheafOfModules.{u} (A.obj ⋙ forget₂ CommRingCat RingCat) :=
  Functor.prod (directForgetFunctor A) (directForgetFunctor A)

noncomputable def sheafifiedExtensionTensorSourceFunctor :
    Modules A × Modules A ⥤ Modules B :=
  directForgetPairFunctor (A := A) ⋙
    extensionTensorSourceFunctor alpha.hom ⋙
      directSheafificationFunctor B

noncomputable def sheafifiedExtensionTensorTargetFunctor :
    Modules A × Modules A ⥤ Modules B :=
  directForgetPairFunctor (A := A) ⋙
    extensionTensorTargetFunctor alpha.hom ⋙
      directSheafificationFunctor B

private lemma sheafifiedExtensionTensorIso_naturality
    {X Y : Modules A × Modules A} (f : X ⟶ Y) :
    (sheafifiedExtensionTensorSourceFunctor alpha).map f ≫
        (sheafifiedExtensionTensorIso alpha Y.1 Y.2).hom =
      (sheafifiedExtensionTensorIso alpha X.1 X.2).hom ≫
        (sheafifiedExtensionTensorTargetFunctor alpha).map f := by
  change (directSheafificationFunctor B).map
      ((extensionTensorSourceFunctor alpha.hom).map
        ((directForgetPairFunctor (A := A)).map f)) ≫
      (directSheafificationFunctor B).map
        ((extensionTensorPresheafNatIso alpha.hom).hom.app
          ((directForgetPairFunctor (A := A)).obj Y)) =
    (directSheafificationFunctor B).map
        ((extensionTensorPresheafNatIso alpha.hom).hom.app
          ((directForgetPairFunctor (A := A)).obj X)) ≫
      (directSheafificationFunctor B).map
        ((extensionTensorTargetFunctor alpha.hom).map
          ((directForgetPairFunctor (A := A)).map f))
  rw [← (directSheafificationFunctor B).map_comp,
    ← (directSheafificationFunctor B).map_comp]
  exact congrArg (directSheafificationFunctor B).map
    ((extensionTensorPresheafNatIso alpha.hom).hom.naturality
      ((directForgetPairFunctor (A := A)).map f))

/-- Naturality of the sheafified base-change comparison. -/
noncomputable def sheafifiedExtensionTensorNatIso :
    sheafifiedExtensionTensorSourceFunctor alpha ≅
      sheafifiedExtensionTensorTargetFunctor alpha :=
  NatIso.ofComponents
    (fun MN => sheafifiedExtensionTensorIso alpha MN.1 MN.2)
    (fun f => sheafifiedExtensionTensorIso_naturality alpha f)

end

end LSZ.CommRingSheaf
