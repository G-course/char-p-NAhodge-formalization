import LSZ.SheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace LSZ.CommRingSheaf

universe u v₁ u₁

noncomputable section

section Presheaf

variable {C : Type u₁} [Category.{v₁} C]
  {A B : Functor Cᵒᵖ CommRingCat.{u}} (alpha : A ⟶ B)
  (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))

def mappedSection {U V : Cᵒᵖ} (i : U ⟶ V) (m : M.obj U) : M.obj V := by
  exact M.map i m

@[simp]
lemma mappedSection_add {U V : Cᵒᵖ} (i : U ⟶ V) (m n : M.obj U) :
    mappedSection M i (m + n) = mappedSection M i m + mappedSection M i n := by
  exact map_add (M.map i).hom m n

lemma mappedSection_smul {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : A.obj U) (m : M.obj U) :
    mappedSection M i (r • m) = A.map i r • mappedSection M i m := by
  exact M.map_smul i r m

def extensionUnit (U : Cᵒᵖ) (m : M.obj U) :
    (ModuleCat.extendScalars (alpha.app U).hom).obj (M.obj U) := by
  exact (ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).unit.app (M.obj U) m

@[simp]
lemma extensionUnit_add (U : Cᵒᵖ) (m n : M.obj U) :
    extensionUnit alpha M U (m + n) =
      extensionUnit alpha M U m + extensionUnit alpha M U n := by
  exact map_add ((ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).unit.app (M.obj U)).hom m n

lemma extensionUnit_smul (U : Cᵒᵖ) (r : A.obj U) (m : M.obj U) :
    extensionUnit alpha M U (r • m) =
      alpha.app U r • extensionUnit alpha M U m := by
  exact map_smul ((ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).unit.app (M.obj U)).hom r m

private def extensionAdjointMapToFun {U V : Cᵒᵖ} (i : U ⟶ V) :
    M.obj U →
      (ModuleCat.restrictScalars (alpha.app U).hom).obj
        ((ModuleCat.restrictScalars (B.map i).hom).obj
          ((ModuleCat.extendScalars (alpha.app V).hom).obj (M.obj V))) :=
  fun m ↦ extensionUnit alpha M V (mappedSection M i m)

private lemma extensionAdjointMapToFun_add {U V : Cᵒᵖ} (i : U ⟶ V)
    (m n : M.obj U) :
    extensionAdjointMapToFun alpha M i (m + n) =
      extensionAdjointMapToFun alpha M i m +
        extensionAdjointMapToFun alpha M i n := by
  change extensionUnit alpha M V (mappedSection M i (m + n)) =
    extensionUnit alpha M V (mappedSection M i m) +
      extensionUnit alpha M V (mappedSection M i n)
  rw [mappedSection_add, extensionUnit_add]

private lemma extensionAdjointMapToFun_smul {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : A.obj U) (m : M.obj U) :
    extensionAdjointMapToFun alpha M i (r • m) =
      r • extensionAdjointMapToFun alpha M i m := by
  change extensionUnit alpha M V (mappedSection M i (r • m)) =
    B.map i (alpha.app U r) • extensionUnit alpha M V (mappedSection M i m)
  rw [mappedSection_smul, extensionUnit_smul]
  have hr := CategoryTheory.congr_fun (alpha.naturality i) r
  change alpha.app V (A.map i r) = B.map i (alpha.app U r) at hr
  rw [hr]

noncomputable def extensionAdjointMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    M.obj U ⟶
      (ModuleCat.restrictScalars (alpha.app U).hom).obj
        ((ModuleCat.restrictScalars (B.map i).hom).obj
          ((ModuleCat.extendScalars (alpha.app V).hom).obj (M.obj V))) := by
  exact ModuleCat.ofHom
    (X := M.obj U)
    (Y := (ModuleCat.restrictScalars (alpha.app U).hom).obj
      ((ModuleCat.restrictScalars (B.map i).hom).obj
        ((ModuleCat.extendScalars (alpha.app V).hom).obj (M.obj V))))
    { toFun := extensionAdjointMapToFun alpha M i
      map_add' := extensionAdjointMapToFun_add alpha M i
      map_smul' := extensionAdjointMapToFun_smul alpha M i }

@[simp]
lemma extensionAdjointMap_apply {U V : Cᵒᵖ} (i : U ⟶ V) (m : M.obj U) :
    extensionAdjointMap alpha M i m =
      extensionUnit alpha M V (mappedSection M i m) := by
  rfl

noncomputable def extensionPresheafMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (alpha.app U).hom).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (B.map i).hom).obj
        ((ModuleCat.extendScalars (alpha.app V).hom).obj (M.obj V)) :=
  ((ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv _ _).symm
    (extensionAdjointMap alpha M i)

@[simp]
lemma extensionPresheafMap_unit {U V : Cᵒᵖ} (i : U ⟶ V)
    (m : M.obj U) :
    extensionPresheafMap alpha M i (extensionUnit alpha M U m) =
      extensionUnit alpha M V (mappedSection M i m) := by
  let N := (ModuleCat.restrictScalars (B.map i).hom).obj
    ((ModuleCat.extendScalars (alpha.app V).hom).obj (M.obj V))
  let e := (ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv
    (M.obj U) N
  let h : M.obj U ⟶
      (ModuleCat.restrictScalars (alpha.app U).hom).obj N :=
    extensionAdjointMap alpha M i
  have he := congrArg (fun q ↦ q m) (e.apply_symm_apply h)
  rw [Adjunction.homEquiv_unit] at he
  change e.symm h (extensionUnit alpha M U m) = h m at he
  change e.symm h (extensionUnit alpha M U m) =
    extensionUnit alpha M V (mappedSection M i m)
  exact he

lemma extensionHom_ext (U : Cᵒᵖ)
    {N : ModuleCat.{u} (B.obj U)}
    {f g : (ModuleCat.extendScalars (alpha.app U).hom).obj (M.obj U) ⟶ N}
    (h : ∀ m, f (extensionUnit alpha M U m) =
      g (extensionUnit alpha M U m)) : f = g := by
  let e := (ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv
    (M.obj U) N
  apply e.injective
  apply ModuleCat.hom_ext
  ext m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h m

private lemma extensionPresheaf_map_id (U : Cᵒᵖ) :
    extensionPresheafMap alpha M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (B.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom
          ((B ⋙ forget₂ CommRingCat RingCat).map_id U))).inv.app _ := by
  apply extensionHom_ext alpha M U
  intro m
  rw [extensionPresheafMap_unit]
  change extensionUnit alpha M U (mappedSection M (𝟙 U) m) = _
  change extensionUnit alpha M U (M.map (𝟙 U) m) = _
  rw [PresheafOfModules.map_id]
  rfl

private lemma extensionPresheaf_map_comp {U V W : Cᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    extensionPresheafMap alpha M (i ≫ j) =
      extensionPresheafMap alpha M i ≫
        (ModuleCat.restrictScalars (B.map i).hom).map
          (extensionPresheafMap alpha M j) ≫
        (ModuleCat.restrictScalarsComp' (B.map i).hom (B.map j).hom
          (B.map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom
            ((B ⋙ forget₂ CommRingCat RingCat).map_comp i j))).inv.app _ := by
  apply extensionHom_ext alpha M _
  intro m
  rw [extensionPresheafMap_unit]
  simp only [CategoryTheory.comp_apply, ModuleCat.restrictScalars.map_apply]
  rw [extensionPresheafMap_unit, extensionPresheafMap_unit]
  have hm : mappedSection M (i ≫ j) m =
      mappedSection M j (mappedSection M i m) := by
    exact M.map_comp_apply i j m
  rw [hm]
  rfl

private noncomputable def extensionPresheafObj (U : Cᵒᵖ) :
    ModuleCat.{u} (B.obj U) :=
  (ModuleCat.extendScalars (alpha.app U).hom).obj (M.obj U)

/-- Objectwise extension of scalars for presheaves of modules. -/
noncomputable def extensionPresheaf :
    PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) where
  obj := extensionPresheafObj alpha M
  map := extensionPresheafMap alpha M
  map_id := extensionPresheaf_map_id alpha M
  map_comp := extensionPresheaf_map_comp alpha M

lemma extensionUnit_naturality
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (U : Cᵒᵖ) (m : M.obj U) :
    (ModuleCat.extendScalars (alpha.app U).hom).map (f.app U)
        (extensionUnit alpha M U m) =
      extensionUnit alpha N U (f.app U m) := by
  have h := congrArg (fun q ↦ q m)
    ((ModuleCat.extendRestrictScalarsAdj
      (alpha.app U).hom).unit.naturality (f.app U))
  exact h.symm

private noncomputable def extensionPresheafHomApp
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (U : Cᵒᵖ) :
    (extensionPresheaf alpha M).obj U ⟶
      (extensionPresheaf alpha N).obj U :=
  (ModuleCat.extendScalars (alpha.app U).hom).map (f.app U)

private lemma extensionPresheafHom_naturality
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) {U V : Cᵒᵖ} (i : U ⟶ V) :
    extensionPresheafMap alpha M i ≫
        (ModuleCat.restrictScalars (B.map i).hom).map
          ((ModuleCat.extendScalars (alpha.app V).hom).map (f.app V)) =
      (ModuleCat.extendScalars (alpha.app U).hom).map (f.app U) ≫
        extensionPresheafMap alpha N i := by
  apply extensionHom_ext alpha M U
  intro m
  simp only [CategoryTheory.comp_apply, ModuleCat.restrictScalars.map_apply]
  rw [extensionPresheafMap_unit, extensionUnit_naturality,
    extensionUnit_naturality, extensionPresheafMap_unit]
  have hf : f.app V (mappedSection M i m) =
      mappedSection N i (f.app U m) := by
    exact PresheafOfModules.naturality_apply f i m
  rw [hf]

noncomputable def extensionPresheafHom
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) : extensionPresheaf alpha M ⟶ extensionPresheaf alpha N where
  app := extensionPresheafHomApp alpha f
  naturality := extensionPresheafHom_naturality alpha f

private lemma extensionPresheafHom_id
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    extensionPresheafHom alpha (𝟙 M) = 𝟙 (extensionPresheaf alpha M) := by
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (alpha.app U).hom).map_id (M.obj U)

private lemma extensionPresheafHom_comp
    {M N P : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (g : N ⟶ P) :
    extensionPresheafHom alpha (f ≫ g) =
      extensionPresheafHom alpha f ≫ extensionPresheafHom alpha g := by
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (alpha.app U).hom).map_comp (f.app U) (g.app U)

private noncomputable def extensionPresheafFunctorObj
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat) :=
  extensionPresheaf alpha M

private noncomputable def extensionPresheafFunctorMap
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) :
    extensionPresheafFunctorObj alpha M ⟶
      extensionPresheafFunctorObj alpha N :=
  extensionPresheafHom alpha f

/-- Objectwise extension of scalars is functorial on module presheaves. -/
noncomputable def extensionPresheafFunctor :
    Functor
      (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
      (PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)) where
  obj := extensionPresheafFunctorObj alpha
  map := extensionPresheafFunctorMap alpha
  map_id := extensionPresheafHom_id alpha
  map_comp := extensionPresheafHom_comp alpha

abbrev ringMap :
    (A ⋙ forget₂ CommRingCat RingCat) ⟶
      (B ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight alpha (forget₂ CommRingCat RingCat)

lemma extensionHomEquiv_apply
    (N : ModuleCat.{u} (B.obj U))
    (f : (ModuleCat.extendScalars (alpha.app U).hom).obj (M.obj U) ⟶ N)
    (m : M.obj U) :
    (ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv
        (M.obj U) N f m = f (extensionUnit alpha M U m) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma extensionHomEquiv_symm_unit
    (N : ModuleCat.{u} (B.obj U))
    (g : M.obj U ⟶ (ModuleCat.restrictScalars (alpha.app U).hom).obj N)
    (m : M.obj U) :
    ((ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv
        (M.obj U) N).symm g (extensionUnit alpha M U m) = g m := by
  have h := congrArg (fun q ↦ q m)
    (((ModuleCat.extendRestrictScalarsAdj (alpha.app U).hom).homEquiv
      (M.obj U) N).apply_symm_apply g)
  rw [extensionHomEquiv_apply] at h
  exact h

noncomputable def extensionToRestrictionApp
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (f : extensionPresheaf alpha M ⟶ N) (U : Cᵒᵖ) :
    M.obj U ⟶
      (ModuleCat.restrictScalars (alpha.app U).hom).obj (N.obj U) :=
  (ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv (M.obj U) (N.obj U) (f.app U)

@[simp]
lemma extensionToRestrictionApp_apply
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (f : extensionPresheaf alpha M ⟶ N) (U : Cᵒᵖ) (m : M.obj U) :
    extensionToRestrictionApp alpha M N f U m =
      f.app U (extensionUnit alpha M U m) := by
  exact extensionHomEquiv_apply alpha M (N.obj U) (f.app U) m

private lemma extensionToRestrictionApp_naturality
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (f : extensionPresheaf alpha M ⟶ N) {U V : Cᵒᵖ} (i : U ⟶ V) :
    M.map i ≫ (ModuleCat.restrictScalars (A.map i).hom).map
        (extensionToRestrictionApp alpha M N f V) =
      extensionToRestrictionApp alpha M N f U ≫
        ((PresheafOfModules.restrictScalars (ringMap alpha)).obj N).map i := by
  apply ModuleCat.hom_ext
  ext m
  change extensionToRestrictionApp alpha M N f V (mappedSection M i m) =
    mappedSection N i (extensionToRestrictionApp alpha M N f U m)
  rw [extensionToRestrictionApp_apply, extensionToRestrictionApp_apply]
  have hf := PresheafOfModules.naturality_apply f i
    (extensionUnit alpha M U m)
  change f.app V
      (extensionPresheafMap alpha M i (extensionUnit alpha M U m)) =
    mappedSection N i (f.app U (extensionUnit alpha M U m)) at hf
  rw [extensionPresheafMap_unit] at hf
  exact hf

noncomputable def extensionToRestriction
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (f : extensionPresheaf alpha M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N where
  app := extensionToRestrictionApp alpha M N f
  naturality := extensionToRestrictionApp_naturality alpha M N f

noncomputable def restrictionToExtensionApp
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N)
    (U : Cᵒᵖ) :
    (extensionPresheaf alpha M).obj U ⟶ N.obj U :=
  ((ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv (M.obj U) (N.obj U)).symm (g.app U)

@[simp]
lemma restrictionToExtensionApp_unit
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N)
    (U : Cᵒᵖ) (m : M.obj U) :
    restrictionToExtensionApp alpha M N g U (extensionUnit alpha M U m) =
      g.app U m := by
  exact extensionHomEquiv_symm_unit alpha M (N.obj U) (g.app U) m

private lemma restrictionToExtensionApp_naturality
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    extensionPresheafMap alpha M i ≫
        (ModuleCat.restrictScalars (B.map i).hom).map
          (restrictionToExtensionApp alpha M N g V) =
      restrictionToExtensionApp alpha M N g U ≫ N.map i := by
  apply extensionHom_ext alpha M U
  intro m
  change restrictionToExtensionApp alpha M N g V
      (extensionPresheafMap alpha M i (extensionUnit alpha M U m)) =
    N.map i (restrictionToExtensionApp alpha M N g U
      (extensionUnit alpha M U m))
  rw [extensionPresheafMap_unit, restrictionToExtensionApp_unit,
    restrictionToExtensionApp_unit]
  exact PresheafOfModules.naturality_apply g i m

noncomputable def restrictionToExtension
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N) :
    extensionPresheaf alpha M ⟶ N where
  app := restrictionToExtensionApp alpha M N g
  naturality := restrictionToExtensionApp_naturality alpha M N g

private lemma extensionPresheafHom_left_inv
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (f : extensionPresheaf alpha M ⟶ N) :
    restrictionToExtension alpha M N (extensionToRestriction alpha M N f) = f := by
  apply PresheafOfModules.hom_ext
  intro U
  exact ((ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv (M.obj U) (N.obj U)).symm_apply_apply (f.app U)

private lemma extensionPresheafHom_right_inv
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N) :
    extensionToRestriction alpha M N (restrictionToExtension alpha M N g) = g := by
  apply PresheafOfModules.hom_ext
  intro U
  exact ((ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv (M.obj U) (N.obj U)).apply_symm_apply (g.app U)

noncomputable def extensionPresheafHomEquiv
    (N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)) :
    (extensionPresheaf alpha M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N) where
  toFun := extensionToRestriction alpha M N
  invFun := restrictionToExtension alpha M N
  left_inv := extensionPresheafHom_left_inv alpha M N
  right_inv := extensionPresheafHom_right_inv alpha M N

private lemma extensionPresheafHomEquiv_naturality_left_symm
    {M' M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {N : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)}
    (f : M' ⟶ M)
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap alpha)).obj N) :
    (extensionPresheafHomEquiv alpha M' N).symm (f ≫ g) =
      (extensionPresheafFunctor alpha).map f ≫
        (extensionPresheafHomEquiv alpha M N).symm g := by
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv_naturality_left_symm (f.app U) (g.app U)

private lemma extensionPresheafHomEquiv_naturality_right
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {N N' : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)}
    (f : (extensionPresheafFunctor alpha).obj M ⟶ N) (g : N ⟶ N') :
    extensionPresheafHomEquiv alpha M N' (f ≫ g) =
      extensionPresheafHomEquiv alpha M N f ≫
        (PresheafOfModules.restrictScalars (ringMap alpha)).map g := by
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendRestrictScalarsAdj
    (alpha.app U).hom).homEquiv_naturality_right (f.app U) (g.app U)

private noncomputable def extensionRestrictionPresheafCoreHomEquiv :
    Adjunction.CoreHomEquiv (extensionPresheafFunctor alpha)
      (PresheafOfModules.restrictScalars (ringMap alpha)) where
  homEquiv := extensionPresheafHomEquiv alpha
  homEquiv_naturality_left_symm := extensionPresheafHomEquiv_naturality_left_symm alpha
  homEquiv_naturality_right := extensionPresheafHomEquiv_naturality_right alpha

/-- Objectwise extension of scalars is left adjoint to restriction of scalars
for presheaves of modules. -/
noncomputable def extensionRestrictionPresheafAdjunction :
    extensionPresheafFunctor alpha ⊣
      PresheafOfModules.restrictScalars (ringMap alpha) :=
  Adjunction.mkOfHomEquiv (extensionRestrictionPresheafCoreHomEquiv alpha)

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (alpha : A ⟶ B)

local instance locallyInjectiveId
    (P : Functor Cᵒᵖ RingCat.{u}) :
    Presheaf.IsLocallyInjective J (𝟙 P) :=
  Presheaf.isLocallyInjective_of_injective J (𝟙 P)
    (fun _ ↦ Function.injective_id)

local instance locallySurjectiveId
    (P : Functor Cᵒᵖ RingCat.{u}) :
    Presheaf.IsLocallySurjective J (𝟙 P) :=
  Presheaf.isLocallySurjective_of_surjective J (𝟙 P)
    (fun _ ↦ Function.surjective_id)

abbrev sheafRingMap : ringSheaf A ⟶ ringSheaf B :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map alpha

abbrev directRingMap (B : Sheaf J CommRingCat.{u}) :
    (B.obj ⋙ forget₂ CommRingCat RingCat) ⟶ (ringSheaf B).obj := by
  change (B.obj ⋙ forget₂ CommRingCat RingCat) ⟶
    (B.obj ⋙ forget₂ CommRingCat RingCat)
  exact 𝟙 _

local instance locallyInjectiveDirectRingMap (B : Sheaf J CommRingCat.{u}) :
    Presheaf.IsLocallyInjective J (directRingMap B) := by
  change Presheaf.IsLocallyInjective J
    (𝟙 (B.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

local instance locallySurjectiveDirectRingMap (B : Sheaf J CommRingCat.{u}) :
    Presheaf.IsLocallySurjective J (directRingMap B) := by
  change Presheaf.IsLocallySurjective J
    (𝟙 (B.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

noncomputable def directSheafificationFunctor (B : Sheaf J CommRingCat.{u}) :
    Functor
      (PresheafOfModules.{u} (B.obj ⋙ forget₂ CommRingCat RingCat))
      (Modules B) :=
  PresheafOfModules.sheafification (directRingMap B)

noncomputable def directSheafificationAdjunction (B : Sheaf J CommRingCat.{u}) :
    directSheafificationFunctor B ⊣
      SheafOfModules.forget (ringSheaf B) ⋙
        PresheafOfModules.restrictScalars (directRingMap B) :=
  PresheafOfModules.sheafificationAdjunction (directRingMap B)

/-- The module-linear unit from a presheaf of modules to its direct
sheafification.  Its underlying additive-presheaf map is mathlib's
`CategoryTheory.toSheafify`. -/
noncomputable def directSheafificationUnit (B : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules (B.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((directSheafificationFunctor B).obj P).val :=
  (directSheafificationAdjunction B).unit.app P ≫
    unrestrictId B ((directSheafificationFunctor B).obj P).val

@[simp]
lemma directSheafificationUnit_app_apply
    (B : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules (B.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) :
    (directSheafificationUnit B P).app U x =
      (CategoryTheory.toSheafify J P.presheaf).app U x := rfl

lemma directSheafificationUnit_map_smul
    (B : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules (B.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (a : B.obj.obj U) (x : P.obj U) :
    (directSheafificationUnit B P).app U (a • x) =
      a • (directSheafificationUnit B P).app U x :=
  map_smul ((directSheafificationUnit B P).app U).hom a x

private noncomputable def directForgetFunctorObj
    (A : Sheaf J CommRingCat.{u}) (M : Modules A) :
    PresheafOfModules (A.obj ⋙ forget₂ CommRingCat RingCat) :=
  directPresheaf A M

private noncomputable def directForgetFunctorMap
    (A : Sheaf J CommRingCat.{u}) {M N : Modules A} (f : M ⟶ N) :
    directForgetFunctorObj A M ⟶ directForgetFunctorObj A N :=
  directHom A f

/-- The fully faithful forgetful functor, with its target written directly as
the presheaf underlying the commutative-ring sheaf. -/
noncomputable def directForgetFunctor (A : Sheaf J CommRingCat.{u}) :
    Functor (Modules A)
      (PresheafOfModules (A.obj ⋙ forget₂ CommRingCat RingCat)) where
  obj := directForgetFunctorObj A
  map := directForgetFunctorMap A
  map_id M := directHom_id A M
  map_comp f g := directHom_comp A f g

private noncomputable def directForgetPreimage
    (A : Sheaf J CommRingCat.{u}) {M N : Modules A}
    (f : (directForgetFunctor A).obj M ⟶
      (directForgetFunctor A).obj N) : M ⟶ N :=
  ⟨f⟩

noncomputable def directForgetFullyFaithful (A : Sheaf J CommRingCat.{u}) :
    (directForgetFunctor A).FullyFaithful where
  preimage := directForgetPreimage A

/-- Extension of scalars for sheaves of modules: apply mathlib's
`ModuleCat.extendScalars` on every object and then sheafify. -/
noncomputable abbrev extensionScalarsFunctor :
    Functor (Modules A) (Modules B) :=
  directForgetFunctor A ⋙
    extensionPresheafFunctor alpha.hom ⋙
      directSheafificationFunctor B

private noncomputable abbrev restrictionComparisonSource (N : Modules B) :=
    (directForgetFunctor A).obj
      ((SheafOfModules.restrictScalars (sheafRingMap alpha)).obj N)

private noncomputable abbrev restrictionComparisonTarget (N : Modules B) :=
  (PresheafOfModules.restrictScalars (ringMap alpha.hom)).obj
    ((SheafOfModules.forget (ringSheaf B) ⋙
      PresheafOfModules.restrictScalars (directRingMap B)).obj N)

/-- The objectwise scalar-restriction comparison. -/
noncomputable def restrictionComparisonAppIso (N : Modules B) (U : Cᵒᵖ) :
    (restrictionComparisonSource alpha N).obj U ≅
      (restrictionComparisonTarget alpha N).obj U :=
  ModuleCat.restrictScalarsComp'App
    (alpha.hom.app U).hom ((directRingMap B).app U).hom
    ((sheafRingMap alpha).hom.app U).hom (by rfl) (N.val.obj U)

private lemma restrictionComparisonAppIso_naturality (N : Modules B)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (restrictionComparisonSource alpha N).map f ≫
        (ModuleCat.restrictScalars
          (((A.obj ⋙ forget₂ CommRingCat RingCat).map f).hom)).map
            (restrictionComparisonAppIso alpha N V).hom =
      (restrictionComparisonAppIso alpha N U).hom ≫
        (restrictionComparisonTarget alpha N).map f := by
  ext x
  rfl

/-- Restricting a module sheaf along `alpha` agrees, on the underlying
presheaf, with the two successive restrictions used by the two adjunctions. -/
noncomputable def restrictionComparison (N : Modules B) :
    restrictionComparisonSource alpha N ≅ restrictionComparisonTarget alpha N :=
  PresheafOfModules.isoMk
    (fun U => restrictionComparisonAppIso alpha N U)
    (fun {U V} f => restrictionComparisonAppIso_naturality alpha N (U := U) (V := V) f)

noncomputable def extensionRestrictionHomEquiv (M : Modules A) (N : Modules B) :
    ((extensionScalarsFunctor alpha).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars (sheafRingMap alpha)).obj N) := by
  change ((directSheafificationFunctor B).obj
      ((extensionPresheafFunctor alpha.hom).obj
        ((directForgetFunctor A).obj M)) ⟶ N) ≃ _
  exact ((directSheafificationAdjunction B).homEquiv _ _).trans <|
    (((extensionRestrictionPresheafAdjunction alpha.hom).homEquiv
        ((directForgetFunctor A).obj M)
        ((SheafOfModules.forget (ringSheaf B) ⋙
          PresheafOfModules.restrictScalars (directRingMap B)).obj N)).trans
      (Iso.homCongr (Iso.refl _)
        (restrictionComparison alpha N).symm)).trans
      ((directForgetFullyFaithful A).homEquiv
        (X := M)
        (Y := (SheafOfModules.restrictScalars
          (sheafRingMap alpha)).obj N)).symm

private lemma extensionRestrictionHomEquiv_naturality_left_symm
    {M' M : Modules A} {N : Modules B} (f : M' ⟶ M)
    (g : M ⟶ (SheafOfModules.restrictScalars (sheafRingMap alpha)).obj N) :
    (extensionRestrictionHomEquiv alpha M' N).symm (f ≫ g) =
      (extensionScalarsFunctor alpha).map f ≫
        (extensionRestrictionHomEquiv alpha M N).symm g := by
  dsimp [extensionRestrictionHomEquiv, extensionScalarsFunctor]
  dsimp [Functor.FullyFaithful.homEquiv]
  erw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.map_comp, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Category.assoc]

private lemma extensionRestrictionHomEquiv_naturality_right
    {M : Modules A} {N N' : Modules B}
    (f : (extensionScalarsFunctor alpha).obj M ⟶ N) (g : N ⟶ N') :
    extensionRestrictionHomEquiv alpha M N' (f ≫ g) =
      extensionRestrictionHomEquiv alpha M N f ≫
        (SheafOfModules.restrictScalars (sheafRingMap alpha)).map g := by
  tauto

private noncomputable def extensionRestrictionCoreHomEquiv :
    Adjunction.CoreHomEquiv (extensionScalarsFunctor alpha)
      (SheafOfModules.restrictScalars (sheafRingMap alpha)) where
  homEquiv := extensionRestrictionHomEquiv alpha
  homEquiv_naturality_left_symm := extensionRestrictionHomEquiv_naturality_left_symm alpha
  homEquiv_naturality_right := extensionRestrictionHomEquiv_naturality_right alpha

/-- Extension of scalars for module sheaves is left adjoint to restriction
of scalars. -/
noncomputable def extensionRestrictionAdjunction :
    extensionScalarsFunctor alpha ⊣
      SheafOfModules.restrictScalars (sheafRingMap alpha) :=
  Adjunction.mkOfHomEquiv (extensionRestrictionCoreHomEquiv alpha)

private noncomputable abbrev unchangedSitePushforward :=
    SheafOfModules.pushforward.{u} (J := J) (K := J) (F := 𝟭 C)
      (S := ringSheaf A) (R := ringSheaf B) (sheafRingMap alpha)

private noncomputable abbrev unchangedSiteRestriction :=
  SheafOfModules.restrictScalars.{u} (sheafRingMap alpha)

/-- The sectionwise identity comparison between unchanged-site pushforward
and restriction of scalars. -/
noncomputable def pushforwardRestrictionSectionIso (N : Modules B) (U : Cᵒᵖ) :
    ((SheafOfModules.forget (ringSheaf A)).obj
      ((unchangedSitePushforward alpha).obj N)).obj U ≅
    ((SheafOfModules.forget (ringSheaf A)).obj
      ((unchangedSiteRestriction alpha).obj N)).obj U :=
  Iso.refl _

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma pushforwardRestrictionSectionIso_naturality (N : Modules B)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((SheafOfModules.forget (ringSheaf A)).obj
        ((unchangedSitePushforward alpha).obj N)).map f ≫
      (ModuleCat.restrictScalars
        (((ringSheaf A).obj.map f).hom)).map
          (pushforwardRestrictionSectionIso alpha N V).hom =
    (pushforwardRestrictionSectionIso alpha N U).hom ≫
      ((SheafOfModules.forget (ringSheaf A)).obj
        ((unchangedSiteRestriction alpha).obj N)).map f := by
  ext x
  rfl

/-- The underlying-presheaf comparison for one module sheaf on an unchanged
site. -/
noncomputable def pushforwardRestrictionPresheafIso (N : Modules B) :
    (SheafOfModules.forget (ringSheaf A)).obj
        ((unchangedSitePushforward alpha).obj N) ≅
      (SheafOfModules.forget (ringSheaf A)).obj
        ((unchangedSiteRestriction alpha).obj N) :=
  PresheafOfModules.isoMk
    (fun U => pushforwardRestrictionSectionIso alpha N U)
    (fun {U V} f =>
      pushforwardRestrictionSectionIso_naturality alpha N (U := U) (V := V) f)

/-- The comparison for one module sheaf on an unchanged site. -/
noncomputable def pushforwardRestrictionObjIso (N : Modules B) :
    (unchangedSitePushforward alpha).obj N ≅
      (unchangedSiteRestriction alpha).obj N :=
  (SheafOfModules.fullyFaithfulForget (ringSheaf A)).preimageIso
    (pushforwardRestrictionPresheafIso alpha N)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma pushforwardRestrictionObjIso_naturality
    {M N : Modules B} (f : M ⟶ N) :
    (unchangedSitePushforward alpha).map f ≫
        (pushforwardRestrictionObjIso alpha N).hom =
      (pushforwardRestrictionObjIso alpha M).hom ≫
        (unchangedSiteRestriction alpha).map f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

/-- On an unchanged site, mathlib's pushforward is restriction of scalars. -/
noncomputable def pushforwardRestrictionIso :
    unchangedSitePushforward alpha ≅ unchangedSiteRestriction alpha :=
  NatIso.ofComponents
    (pushforwardRestrictionObjIso alpha)
    (pushforwardRestrictionObjIso_naturality alpha)

local instance restrictionIsRightAdjoint :
    (SheafOfModules.restrictScalars.{u}
      (sheafRingMap alpha)).IsRightAdjoint :=
  (extensionRestrictionAdjunction alpha).isRightAdjoint

local instance pushforwardIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (J := J) (K := J) (F := 𝟭 C)
      (S := ringSheaf A) (R := ringSheaf B)
        (sheafRingMap alpha)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardRestrictionIso alpha).symm

noncomputable def extensionPushforwardAdjunction :
    extensionScalarsFunctor alpha ⊣
      SheafOfModules.pushforward.{u} (J := J) (K := J) (F := 𝟭 C)
        (S := ringSheaf A) (R := ringSheaf B) (sheafRingMap alpha) :=
  (extensionRestrictionAdjunction alpha).ofNatIsoRight
    (pushforwardRestrictionIso alpha).symm

/-- Extension of scalars followed by sheafification is canonically the
mathlib pullback for a morphism of sheaves of commutative rings on one site. -/
noncomputable def extensionPullbackIso :
    extensionScalarsFunctor alpha ≅
      SheafOfModules.pullback.{u} (J := J) (K := J) (F := 𝟭 C)
        (S := ringSheaf A) (R := ringSheaf B) (sheafRingMap alpha) :=
  Adjunction.leftAdjointUniq (extensionPushforwardAdjunction alpha)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (J := J) (K := J) (F := 𝟭 C)
      (S := ringSheaf A) (R := ringSheaf B) (sheafRingMap alpha))

end Sheaf

end

end LSZ.CommRingSheaf
