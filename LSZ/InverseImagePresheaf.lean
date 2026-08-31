import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Inverse image of a presheaf of modules

The underlying ring and abelian presheaves are mathlib's left-Kan-extension
pullbacks.  We only install the induced module structure on each value and
prove semilinearity of restriction; `PresheafOfModules.ofPresheaf` supplies
all remaining presheaf coherence.
-/

open CategoryTheory Limits Opposite TopologicalSpace

namespace LSZ.InverseImagePresheaf

universe u

noncomputable section

attribute [local instance] IsFiltered.isSifted
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (A : Y.Presheaf CommRingCat.{u})
  (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))

/-- The ring-valued inverse-image presheaf supplied by mathlib. -/
abbrev ring : X.Presheaf CommRingCat.{u} :=
  (TopCat.Presheaf.pullback CommRingCat.{u} f).obj A

/-- The inverse image of the underlying abelian presheaf, supplied by mathlib. -/
abbrev additive : X.Presheaf Ab.{u} :=
  (TopCat.Presheaf.pullback Ab.{u} f).obj M.presheaf

abbrev Index (U : (Opens X)ᵒᵖ) :=
  CostructuredArrow (Opens.map f).op U

abbrev ringDiagram (U : (Opens X)ᵒᵖ) : Index f U ⥤ RingCat.{u} :=
  CostructuredArrow.proj (Opens.map f).op U ⋙ A ⋙
    forget₂ CommRingCat RingCat

abbrev moduleDiagram (U : (Opens X)ᵒᵖ) :
    Index f U ⥤ Ab.{u} :=
  CostructuredArrow.proj (Opens.map f).op U ⋙ M.presheaf

abbrev commRingCocone (U : (Opens X)ᵒᵖ) :
    Cocone (CostructuredArrow.proj (Opens.map f).op U ⋙ A) :=
  (Functor.LeftExtension.mk ((Opens.map f).op.leftKanExtension A)
    ((Opens.map f).op.leftKanExtensionUnit A)).coconeAt U

abbrev ringCocone (U : (Opens X)ᵒᵖ) : Cocone (ringDiagram f A U) :=
  (forget₂ CommRingCat RingCat).mapCocone (commRingCocone f A U)

abbrev moduleCocone (U : (Opens X)ᵒᵖ) :
    Cocone (moduleDiagram f A M U) :=
  (Functor.LeftExtension.mk ((Opens.map f).op.leftKanExtension M.presheaf)
    ((Opens.map f).op.leftKanExtensionUnit M.presheaf)).coconeAt U

noncomputable def ringIsColimit (U : (Opens X)ᵒᵖ) :
    IsColimit (ringCocone f A U) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat)
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit A U)

noncomputable def moduleIsColimit (U : (Opens X)ᵒᵖ) :
    IsColimit (moduleCocone f A M U) :=
  (Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit M.presheaf U

/-- The sectionwise module structure induced by the two Kan colimits. -/
@[instance_reducible]
noncomputable def sectionModule (U : (Opens X)ᵒᵖ) :
    Module ((ring f A ⋙ forget₂ CommRingCat RingCat).obj U)
      ((additive f A M).obj U) := by
  letI (i : Index f U) :
      Module ((ringDiagram f A U).obj i) ((moduleDiagram f A M U).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj
        ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
    infer_instance
  exact IsColimit.module (ringDiagram f A U) (moduleDiagram f A M U)
    (fun q r m ↦ M.map_smul
      (CostructuredArrow.proj (Opens.map f).op U |>.map q) r m)
    (ringIsColimit f A U) (moduleIsColimit f A M U)

local instance (U : (Opens X)ᵒᵖ) :
    Module ((ring f A ⋙ forget₂ CommRingCat RingCat).obj U)
      ((additive f A M).obj U) :=
  sectionModule f A M U

lemma jointly_surjective (U : (Opens X)ᵒᵖ)
    (r : (ring f A ⋙ forget₂ CommRingCat RingCat).obj U)
    (m : (additive f A M).obj U) :
    ∃ (j : Index f U) (a : (ringDiagram f A U).obj j)
      (x : (moduleDiagram f A M U).obj j),
      (ringCocone f A U).ι.app j a = r ∧
        (moduleCocone f A M U).ι.app j x = m := by
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) (ringIsColimit f A U)) r
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget Ab) (moduleIsColimit f A M U)) m
  let k := IsFiltered.max i j
  let eR := IsFiltered.leftToMax i j
  let eM := IsFiltered.rightToMax i j
  refine ⟨k, (ringDiagram f A U).map eR a,
    (moduleDiagram f A M U).map eM x, ?_, ?_⟩
  · calc
      _ = (ringCocone f A U).ι.app i a := by
        simpa only [k, eR, Functor.const_obj_obj,
          CategoryTheory.comp_apply] using
          ConcreteCategory.congr_hom ((ringCocone f A U).w eR) a
      _ = r := ha
  · calc
      _ = (moduleCocone f A M U).ι.app j x := by
        simpa only [k, eM, Functor.const_obj_obj,
          CategoryTheory.comp_apply] using
          ConcreteCategory.congr_hom ((moduleCocone f A M U).w eM) x
      _ = m := hx

lemma map_ring_cocone {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : Index f U) :
    (ringCocone f A U).ι.app j ≫
        (ring f A ⋙ forget₂ CommRingCat RingCat).map q =
      (ringCocone f A V).ι.app ((CostructuredArrow.map q).obj j) := by
  cat_disch

lemma map_module_cocone {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : Index f U) :
    (moduleCocone f A M U).ι.app j ≫ (additive f A M).map q =
      (moduleCocone f A M V).ι.app ((CostructuredArrow.map q).obj j) := by
  cat_disch

lemma map_ring_cocone_apply {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : Index f U) (a : (ringDiagram f A U).obj j) :
    (ring f A ⋙ forget₂ CommRingCat RingCat).map q
        ((ringCocone f A U).ι.app j a) =
      (ringCocone f A V).ι.app ((CostructuredArrow.map q).obj j) a := by
  simpa only [CategoryTheory.comp_apply] using!
    ConcreteCategory.congr_hom (map_ring_cocone f A q j) a

lemma map_module_cocone_apply {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : Index f U) (x : (moduleDiagram f A M U).obj j) :
    (additive f A M).map q ((moduleCocone f A M U).ι.app j x) =
      (moduleCocone f A M V).ι.app ((CostructuredArrow.map q).obj j) x := by
  simpa only [CategoryTheory.comp_apply] using!
    ConcreteCategory.congr_hom (map_module_cocone f A M q j) x

/-- Restriction in the two Kan extensions is semilinear. -/
lemma map_smul {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (r : (ring f A ⋙ forget₂ CommRingCat RingCat).obj U)
    (m : (additive f A M).obj U) :
    (additive f A M).map q (r • m) =
      (ring f A ⋙ forget₂ CommRingCat RingCat).map q r •
        (additive f A M).map q m := by
  letI (i : Index f U) :
      Module ((ringDiagram f A U).obj i) ((moduleDiagram f A M U).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj
        ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
    infer_instance
  letI (i : Index f V) :
      Module ((ringDiagram f A V).obj i) ((moduleDiagram f A M V).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj
        ((CostructuredArrow.proj (Opens.map f).op V).obj i))
      (M.obj ((CostructuredArrow.proj (Opens.map f).op V).obj i))
    infer_instance
  obtain ⟨j, a, x, rfl, rfl⟩ := jointly_surjective f A M U r m
  rw [← IsColimit.ι_smul (ringDiagram f A U) (moduleDiagram f A M U)
    (fun e s y ↦ M.map_smul
      (CostructuredArrow.proj (Opens.map f).op U |>.map e) s y)
    (ringIsColimit f A U) (moduleIsColimit f A M U) j a x]
  rw [map_module_cocone_apply f A M q j,
    map_ring_cocone_apply f A q j,
    map_module_cocone_apply f A M q j]
  exact IsColimit.ι_smul (ringDiagram f A V) (moduleDiagram f A M V)
    (fun e s y ↦ M.map_smul
      (CostructuredArrow.proj (Opens.map f).op V |>.map e) s y)
    (ringIsColimit f A V) (moduleIsColimit f A M V)
    ((CostructuredArrow.map q).obj j) a x

/-- Inverse image as a module presheaf.  All additive-presheaf coherence is
inherited from mathlib's pullback through `ofPresheaf`. -/
noncomputable def module
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (ring f A ⋙ forget₂ CommRingCat RingCat) :=
  letI (U : (Opens X)ᵒᵖ) := sectionModule f A M U
  PresheafOfModules.ofPresheaf (additive f A M)
    (fun {_ _} q r m ↦ by simpa only using map_smul f A M q r m)

@[simp]
lemma module_presheaf : (module f A M).presheaf = additive f A M := rfl

private noncomputable def presheafMap
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) : M.presheaf ⟶ N.presheaf := by
  exact (PresheafOfModules.toPresheaf
    (A ⋙ forget₂ CommRingCat RingCat)).map g

@[simp]
private lemma presheafMap_app_apply
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (U) (m : M.obj U) :
    (presheafMap A g).app U m = g.app U m := rfl

private abbrev additiveMap
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) : additive f A M ⟶ additive f A N :=
  (TopCat.Presheaf.pullback Ab.{u} f).map
    (presheafMap A g)

private lemma additiveMap_cocone_apply
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (U : (Opens X)ᵒᵖ) (j : Index f U)
    (m : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (additiveMap f A g).app U ((moduleCocone f A M U).ι.app j m) =
      (moduleCocone f A N U).ι.app j (g.app _ m) := by
  have h : (moduleCocone f A M U).ι.app j ≫
        (additiveMap f A g).app U =
      (presheafMap A g).app j.left ≫
        (moduleCocone f A N U).ι.app j := by
    dsimp [additiveMap, additive, moduleCocone, TopCat.Presheaf.pullback]
    simp only [Category.assoc, NatTrans.naturality]
    have hunit := NatTrans.congr_app
      ((Opens.map f).op.lanUnit.naturality
        (presheafMap A g)) j.left
    dsimp [Functor.lanUnit] at hunit
    rw [reassoc_of% hunit]
    rfl
  have hm := ConcreteCategory.congr_hom h m
  change (additiveMap f A g).app U ((moduleCocone f A M U).ι.app j m) =
    (moduleCocone f A N U).ι.app j (g.app _ m) at hm
  exact hm

private noncomputable def modulePresheafMap
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) : (module f A M).presheaf ⟶ (module f A N).presheaf := by
  exact additiveMap f A g

private lemma modulePresheafMap_cocone_apply
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (U : (Opens X)ᵒᵖ) (j : Index f U)
    (m : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (modulePresheafMap f A g).app U ((moduleCocone f A M U).ι.app j m) =
      (moduleCocone f A N U).ι.app j (g.app _ m) := by
  have h := additiveMap_cocone_apply f A g U j m
  change (modulePresheafMap f A g).app U
      ((moduleCocone f A M U).ι.app j m) =
    (moduleCocone f A N U).ι.app j (g.app _ m) at h
  exact h

/-- The action of inverse image on a morphism of module presheaves. -/
noncomputable def moduleMap
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) : module f A M ⟶ module f A N :=
  PresheafOfModules.homMk (modulePresheafMap f A g) (fun U r m ↦ by
    letI (i : Index f U) :
        Module ((ringDiagram f A U).obj i) ((moduleDiagram f A M U).obj i) := by
      change Module
        ((A ⋙ forget₂ CommRingCat RingCat).obj
          ((CostructuredArrow.proj (Opens.map f).op U).obj i))
        (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      exact (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i)).isModule
    letI (i : Index f U) :
        Module ((ringDiagram f A U).obj i) ((moduleDiagram f A N U).obj i) := by
      change Module
        ((A ⋙ forget₂ CommRingCat RingCat).obj
          ((CostructuredArrow.proj (Opens.map f).op U).obj i))
        (N.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      exact (N.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i)).isModule
    obtain ⟨j, a, x, rfl, rfl⟩ := jointly_surjective f A M U r m
    rw [← IsColimit.ι_smul (ringDiagram f A U) (moduleDiagram f A M U)
      (fun e s y ↦ M.map_smul
        (CostructuredArrow.proj (Opens.map f).op U |>.map e) s y)
      (ringIsColimit f A U) (moduleIsColimit f A M U) j a x]
    rw [modulePresheafMap_cocone_apply]
    let x' : M.obj
        ((CostructuredArrow.proj (Opens.map f).op U).obj j) := by
      exact x
    change (moduleCocone f A N U).ι.app j (g.app _ (a • x')) =
      (ringCocone f A U).ι.app j a •
        (show (module f A N).obj U from
          (modulePresheafMap f A g).app U
            ((moduleCocone f A M U).ι.app j x'))
    have hg := (g.app _).hom.map_smul a x'
    rw [hg]
    rw [IsColimit.ι_smul (ringDiagram f A U) (moduleDiagram f A N U)
      (fun e s y ↦ N.map_smul
        (CostructuredArrow.proj (Opens.map f).op U |>.map e) s y)
      (ringIsColimit f A U) (moduleIsColimit f A N U)]
    rw [modulePresheafMap_cocone_apply])

@[simp]
lemma moduleMap_cocone_apply
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (U : (Opens X)ᵒᵖ) (j : Index f U)
    (m : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (moduleMap f A g).app U ((moduleCocone f A M U).ι.app j m) =
      (moduleCocone f A N U).ι.app j (g.app _ m) := by
  have h := modulePresheafMap_cocone_apply f A g U j m
  change (moduleMap f A g).app U ((moduleCocone f A M U).ι.app j m) =
    (moduleCocone f A N U).ι.app j (g.app _ m) at h
  exact h

/-- Every inverse-image section is represented on one neighbourhood. -/
lemma module_jointly_surjective
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (m : (module f A M).obj U) :
    ∃ (j : Index f U)
      (x : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)),
      (moduleCocone f A M U).ι.app j x = m := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget Ab) (moduleIsColimit f A M U)) m

private lemma moduleMap_id
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) :
    moduleMap f A (𝟙 M) = 𝟙 (module f A M) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  obtain ⟨j, x, rfl⟩ := module_jointly_surjective f A M U m
  rw [moduleMap_cocone_apply]
  rfl

private lemma moduleMap_comp
    {M N P : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (h : N ⟶ P) :
    moduleMap f A (g ≫ h) = moduleMap f A g ≫ moduleMap f A h := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  obtain ⟨j, x, rfl⟩ := module_jointly_surjective f A M U m
  rw [moduleMap_cocone_apply]
  change (moduleCocone f A P U).ι.app j ((g ≫ h).app _ x) =
    (moduleMap f A h).app U
      ((moduleMap f A g).app U ((moduleCocone f A M U).ι.app j x))
  rw [moduleMap_cocone_apply, moduleMap_cocone_apply]
  rfl

/-- Inverse image of module presheaves as a functor. -/
noncomputable def moduleFunctor :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u}
        (ring f A ⋙ forget₂ CommRingCat RingCat) where
  obj := module f A
  map := moduleMap f A
  map_id := moduleMap_id f A
  map_comp := moduleMap_comp f A

end

end LSZ.InverseImagePresheaf
