import LSZ.ExtensionScalarsTensor
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# Filtered colimits and tensor products over varying rings

For a filtered diagram of commutative rings and compatible diagrams of
modules, this file compares the colimit of the objectwise tensor products
with the tensor product of the two colimit modules.  The module structures on
the colimits are the ones supplied by `Limits.IsColimit.module`.
-/

open CategoryTheory Limits Opposite
open scoped MonoidalCategory TensorProduct

namespace LSZ.FilteredColimitTensor

universe u

noncomputable section

attribute [local instance] IsFiltered.isSifted
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [SmallCategory C] [IsFiltered Cᵒᵖ]
  (R : Cᵒᵖ ⥤ CommRingCat.{u})
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

private abbrev ringDiagram : Cᵒᵖ ⥤ RingCat.{u} :=
  R ⋙ forget₂ CommRingCat RingCat

private abbrev ringCocone : Cocone (ringDiagram R) :=
  (forget₂ CommRingCat RingCat).mapCocone (colimit.cocone R)

private noncomputable def ringIsColimit : IsColimit (ringCocone R) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat) (colimit.isColimit R)

private abbrev moduleCocone
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Cocone Q.presheaf :=
  colimit.cocone Q.presheaf

private noncomputable def moduleIsColimit
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    IsColimit (moduleCocone R Q) :=
  colimit.isColimit Q.presheaf

private noncomputable abbrev ringPoint : CommRingCat.{u} :=
  colimit R

private noncomputable abbrev modulePoint
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) : Ab.{u} :=
  colimit Q.presheaf

/-- The `colimit R`-module structure on the additive colimit of `Q`. -/
@[instance_reducible]
noncomputable def colimitModule
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Module (ringPoint R) (modulePoint R Q) := by
  change Module (ringCocone R).pt (moduleCocone R Q).pt
  letI (i : Cᵒᵖ) : Module ((ringDiagram R).obj i) (Q.presheaf.obj i) := by
    change Module ((R ⋙ forget₂ CommRingCat RingCat).obj i) (Q.obj i)
    infer_instance
  exact IsColimit.module.{u, u, u} (ringDiagram R) Q.presheaf
    (fun f r m ↦ Q.map_smul f r m)
    (ringIsColimit R) (moduleIsColimit R Q)

local instance
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Module (ringPoint R) (modulePoint R Q) :=
  colimitModule R Q

/-- The additive colimit, equipped with its canonical module structure over
the colimit ring. -/
noncomputable def colimitObj
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ModuleCat (ringPoint R) :=
  ModuleCat.of _ (modulePoint R Q)

private def inclusion
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (m : Q.obj i) : colimitObj R Q :=
  (moduleCocone R Q).ι.app i m

@[simp]
private lemma inclusion_zero
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) : inclusion R Q i 0 = 0 :=
  map_zero ((moduleCocone R Q).ι.app i).hom

private lemma inclusion_add
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (m n : Q.obj i) :
    inclusion R Q i (m + n) = inclusion R Q i m + inclusion R Q i n :=
  map_add ((moduleCocone R Q).ι.app i).hom m n

private def ringInclusion (i : Cᵒᵖ) (r : R.obj i) : ringPoint R :=
  (colimit.cocone R).ι.app i r

private lemma inclusion_smul
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (r : R.obj i) (m : Q.obj i) :
    inclusion R Q i (r • m) =
      ringInclusion R i r • inclusion R Q i m := by
  letI (j : Cᵒᵖ) : Module ((ringDiagram R).obj j) (Q.presheaf.obj j) := by
    change Module ((R ⋙ forget₂ CommRingCat RingCat).obj j) (Q.obj j)
    infer_instance
  have h := IsColimit.ι_smul.{u, u, u} (ringDiagram R) Q.presheaf
    (fun f r m ↦ Q.map_smul f r m)
    (ringIsColimit R) (moduleIsColimit R Q) i r m
  change inclusion R Q i (r • m) =
    ringInclusion R i r • inclusion R Q i m at h
  exact h

private lemma jointly_surjective
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (r : ringPoint R) (m : colimitObj R Q) :
    ∃ (i : Cᵒᵖ) (a : R.obj i) (p : Q.obj i),
      ringInclusion R i a = r ∧ inclusion R Q i p = m := by
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit R)) r
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget Ab) (moduleIsColimit R Q)) m
  let k := IsFiltered.max i j
  let eR := IsFiltered.leftToMax i j
  let eM := IsFiltered.rightToMax i j
  refine ⟨k, R.map eR a, Q.map eM p, ?_, ?_⟩
  · calc
      _ = (colimit.cocone R).ι.app i a := by
        have h := ConcreteCategory.congr_hom ((colimit.cocone R).w eR) a
        change ringInclusion R k (R.map eR a) =
          (colimit.cocone R).ι.app i a at h
        exact h
      _ = r := ha
  · calc
      _ = (moduleCocone R Q).ι.app j p := by
        have h := ConcreteCategory.congr_hom ((moduleCocone R Q).w eM) p
        change inclusion R Q k (Q.map eM p) =
          (moduleCocone R Q).ι.app j p at h
        exact h
      _ = m := hp

private lemma inclusion_jointly_surjective
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (m : colimitObj R Q) :
    ∃ (i : Cᵒᵖ) (p : Q.obj i), inclusion R Q i p = m := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget Ab) (moduleIsColimit R Q)) m

private abbrev constantRing : Cᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (ringPoint R)

private abbrev ringMap : R ⟶ constantRing R :=
  (colimit.cocone R).ι

private noncomputable abbrev extendedPresheaf
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u}
      (constantRing R ⋙ forget₂ CommRingCat RingCat) :=
  CommRingSheaf.extensionPresheaf (ringMap R) Q

private noncomputable abbrev extendedObj
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) :=
  (extendedPresheaf R Q).obj i

private noncomputable def extendedMap
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {i j : Cᵒᵖ} (f : i ⟶ j) :
    extendedObj R Q i ⟶ extendedObj R Q j :=
  ModuleCat.ofHom
    { toFun := fun m ↦ (extendedPresheaf R Q).map f m
      map_add' := fun m n ↦ map_add ((extendedPresheaf R Q).map f).hom m n
      map_smul' := fun r m ↦ by
        change (extendedPresheaf R Q).map f (r • m) = r •
          (extendedPresheaf R Q).map f m
        rw [(extendedPresheaf R Q).map_smul]
        rfl }

/-- Extend every object to the single colimit ring. -/
noncomputable def extendedDiagram
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Cᵒᵖ ⥤ ModuleCat (ringPoint R) where
  obj i := extendedObj R Q i
  map f := extendedMap R Q f
  map_id i := by
    apply (forget₂ (ModuleCat (ringPoint R)) Ab).map_injective
    change (extendedPresheaf R Q).presheaf.map (𝟙 i) = 𝟙 _
    simp
  map_comp f g := by
    apply (forget₂ (ModuleCat (ringPoint R)) Ab).map_injective
    change (extendedPresheaf R Q).presheaf.map (f ≫ g) =
      (extendedPresheaf R Q).presheaf.map f ≫
        (extendedPresheaf R Q).presheaf.map g
    simp

/-- The generator `1 ⊗ m` in one object of the extended diagram. -/
def extendedUnit
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (m : Q.obj i) : (extendedDiagram R Q).obj i :=
  CommRingSheaf.extensionUnit (ringMap R) Q i m

@[simp]
lemma extendedUnit_add
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (m n : Q.obj i) :
    extendedUnit R Q i (m + n) =
      extendedUnit R Q i m + extendedUnit R Q i n :=
  CommRingSheaf.extensionUnit_add (ringMap R) Q i m n

@[simp]
lemma extendedUnit_smul
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (r : R.obj i) (m : Q.obj i) :
    extendedUnit R Q i (r • m) =
      ringInclusion R i r • extendedUnit R Q i m := by
  exact CommRingSheaf.extensionUnit_smul (ringMap R) Q i r m

private noncomputable def inclusionLinear
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) :
    Q.obj i ⟶
      (ModuleCat.restrictScalars ((ringMap R).app i).hom).obj
        (colimitObj R Q) :=
  ModuleCat.ofHom (X := Q.obj i)
    (Y := (ModuleCat.restrictScalars ((ringMap R).app i).hom).obj
      (colimitObj R Q))
    { toFun := inclusion R Q i
      map_add' := fun m n ↦ (moduleCocone R Q).ι.app i |>.hom.map_add m n
      map_smul' := fun r m ↦ inclusion_smul R Q i r m }

/-- The canonical leg
`(colim R) ⊗[Rᵢ] Qᵢ ⟶ colim Q`, given by `r ⊗ m ↦ r • ιᵢ(m)`. -/
noncomputable def extendedLeg
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) :
    (extendedDiagram R Q).obj i ⟶ colimitObj R Q :=
  ((ModuleCat.extendRestrictScalarsAdj ((ringMap R).app i).hom).homEquiv _ _).symm
    (inclusionLinear R Q i)

@[simp]
lemma extendedLeg_unit
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (i : Cᵒᵖ) (m : Q.obj i) :
    extendedLeg R Q i (extendedUnit R Q i m) = inclusion R Q i m := by
  have h := CommRingSheaf.extensionHomEquiv_symm_unit
    (ringMap R) Q (colimitObj R Q) (inclusionLinear R Q i) m
  change extendedLeg R Q i (extendedUnit R Q i m) =
    inclusion R Q i m at h
  exact h

@[simp]
lemma extendedDiagram_map_unit
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {i j : Cᵒᵖ} (f : i ⟶ j) (m : Q.obj i) :
    (extendedDiagram R Q).map f (extendedUnit R Q i m) =
      extendedUnit R Q j (Q.map f m) := by
  exact CommRingSheaf.extensionPresheafMap_unit (ringMap R) Q f m

/-- The extended modules map to the original additive colimit. -/
noncomputable def extendedCocone
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Cocone (extendedDiagram R Q) where
  pt := colimitObj R Q
  ι :=
    { app := extendedLeg R Q
      naturality := by
        intro i j f
        apply CommRingSheaf.extensionHom_ext (ringMap R) Q i
        intro m
        change extendedLeg R Q j
            ((extendedDiagram R Q).map f (extendedUnit R Q i m)) =
          extendedLeg R Q i (extendedUnit R Q i m)
        rw [extendedDiagram_map_unit, extendedLeg_unit, extendedLeg_unit]
        exact ConcreteCategory.congr_hom ((moduleCocone R Q).w f) m }

private noncomputable def generatorCocone
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : Cocone (extendedDiagram R Q)) : Cocone Q.presheaf where
  pt := (forget₂ (ModuleCat (ringPoint R)) Ab).obj s.pt
  ι :=
    { app := fun i ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun m ↦ s.ι.app i (extendedUnit R Q i m))
        (fun m n ↦ by
          rw [extendedUnit_add]
          exact map_add (s.ι.app i).hom _ _)
      naturality := by
        intro i j f
        apply (forget Ab).map_injective
        ext m
        have h := ConcreteCategory.congr_hom (s.w f) (extendedUnit R Q i m)
        change s.ι.app j
            ((extendedDiagram R Q).map f (extendedUnit R Q i m)) =
          s.ι.app i (extendedUnit R Q i m) at h
        rwa [extendedDiagram_map_unit] at h }

private noncomputable def generatorDesc
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : Cocone (extendedDiagram R Q)) :
    (moduleCocone R Q).pt ⟶
      (forget₂ (ModuleCat (ringPoint R)) Ab).obj s.pt :=
  (moduleIsColimit R Q).desc (generatorCocone R Q s)

@[simp]
private lemma generatorDesc_inclusion
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : Cocone (extendedDiagram R Q)) (i : Cᵒᵖ) (m : Q.obj i) :
    generatorDesc R Q s (inclusion R Q i m) =
      s.ι.app i (extendedUnit R Q i m) := by
  exact ConcreteCategory.congr_hom
    ((moduleIsColimit R Q).fac (generatorCocone R Q s) i) m

private noncomputable def extendedDesc
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : Cocone (extendedDiagram R Q)) : colimitObj R Q ⟶ s.pt :=
  ModuleCat.ofHom
    { toFun := generatorDesc R Q s
      map_add' := fun m n ↦ (generatorDesc R Q s).hom.map_add m n
      map_smul' := fun r m ↦ by
        obtain ⟨i, a, p, ha, hp⟩ := jointly_surjective R Q r m
        rw [← ha, ← hp, ← inclusion_smul R Q i a p,
          generatorDesc_inclusion, generatorDesc_inclusion,
          extendedUnit_smul]
        exact map_smul (s.ι.app i).hom _ _ }

@[simp]
private lemma extendedDesc_inclusion
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : Cocone (extendedDiagram R Q)) (i : Cᵒᵖ) (m : Q.obj i) :
    extendedDesc R Q s (inclusion R Q i m) =
      s.ι.app i (extendedUnit R Q i m) :=
  generatorDesc_inclusion R Q s i m

/-- Extending all objects to the colimit ring does not change the colimit
module. -/
noncomputable def extendedCoconeIsColimit
    (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    IsColimit (extendedCocone R Q) :=
  IsColimit.mk
    (fun s ↦ extendedDesc R Q s)
    (fun s i ↦ by
      apply CommRingSheaf.extensionHom_ext (ringMap R) Q i
      intro m
      change extendedDesc R Q s
          (extendedLeg R Q i (extendedUnit R Q i m)) =
        s.ι.app i (extendedUnit R Q i m)
      rw [extendedLeg_unit, extendedDesc_inclusion])
    (fun s h hh ↦ by
      apply ModuleCat.hom_ext
      ext m
      obtain ⟨i, p, rfl⟩ := inclusion_jointly_surjective R Q m
      have e := ConcreteCategory.congr_hom (hh i) (extendedUnit R Q i p)
      change h (extendedLeg R Q i (extendedUnit R Q i p)) =
        s.ι.app i (extendedUnit R Q i p) at e
      rw [extendedLeg_unit] at e
      exact e.trans (extendedDesc_inclusion R Q s i p).symm)

/-- Extension of scalars distributes over tensor product at one index. -/
noncomputable def extendedTensorObjIso (i : Cᵒᵖ) :
    (extendedDiagram R (M ⊗ N)).obj i ≅
      ((extendedDiagram R M) ⊗ (extendedDiagram R N)).obj i :=
  CommRingSheaf.extensionTensorSectionIso (ringMap R) M N i

private lemma extendedTensorObjIso_naturality
    {i j : Cᵒᵖ} (f : i ⟶ j) :
    (extendedDiagram R (M ⊗ N)).map f ≫
        (extendedTensorObjIso R M N j).hom =
      (extendedTensorObjIso R M N i).hom ≫
        ((extendedDiagram R M) ⊗ (extendedDiagram R N)).map f := by
  have h := (CommRingSheaf.extensionTensorPresheafIso
    (ringMap R) M N).hom.naturality f
  change (extendedDiagram R (M ⊗ N)).map f ≫
      (extendedTensorObjIso R M N j).hom =
    (extendedTensorObjIso R M N i).hom ≫
      ((extendedDiagram R M) ⊗ (extendedDiagram R N)).map f at h
  exact h

/-- The objectwise base-change isomorphisms form an isomorphism of diagrams. -/
noncomputable def extendedTensorDiagramIso :
    extendedDiagram R (M ⊗ N) ≅
      extendedDiagram R M ⊗ extendedDiagram R N :=
  NatIso.ofComponents (extendedTensorObjIso R M N)
    (extendedTensorObjIso_naturality R M N)

@[simp]
lemma extendedTensorObjIso_hom_unit_tmul
    (i : Cᵒᵖ) (m : M.obj i) (n : N.obj i) :
    (extendedTensorObjIso R M N i).hom
        (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n)) =
      extendedUnit R M i m ⊗ₜ[ringPoint R] extendedUnit R N i n := by
  exact CommRingSheaf.extensionTensorSectionIso_hom_unit_tmul
    (ringMap R) M N i m n

private noncomputable def tensorCocone :
    Cocone (extendedDiagram R (M ⊗ N)) :=
  (Cocone.precompose (extendedTensorDiagramIso R M N).hom).obj
    ((extendedCocone R M).tensor (extendedCocone R N))

private noncomputable def tensorCoconeIsColimit :
    IsColimit (tensorCocone R M N) :=
  (IsColimit.precomposeHomEquiv (extendedTensorDiagramIso R M N)
    ((extendedCocone R M).tensor (extendedCocone R N))).symm
      ((extendedCoconeIsColimit R M).tensor
        (extendedCoconeIsColimit R N))

/-- The colimit of the varying-base tensor products is the tensor product of
the two colimit modules. -/
noncomputable def tensorIso :
    colimitObj R (M ⊗ N) ≅ colimitObj R M ⊗ colimitObj R N :=
  (extendedCoconeIsColimit R (M ⊗ N)).coconePointUniqueUpToIso
    (tensorCoconeIsColimit R M N)

@[simp]
private lemma tensorCocone_ι_unit_tmul
    (i : Cᵒᵖ) (m : M.obj i) (n : N.obj i) :
    (tensorCocone R M N).ι.app i
        (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n)) =
      inclusion R M i m ⊗ₜ[ringPoint R] inclusion R N i n := by
  change ((extendedLeg R M i) ⊗ₘ (extendedLeg R N i))
      ((extendedTensorObjIso R M N i).hom
        (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n))) = _
  rw [extendedTensorObjIso_hom_unit_tmul,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    extendedLeg_unit, extendedLeg_unit]

/-- Formula for the filtered-colimit tensor comparison on a local pure
tensor. -/
@[simp]
lemma tensorIso_hom_inclusion_tmul
    (i : Cᵒᵖ) (m : M.obj i) (n : N.obj i) :
    (tensorIso R M N).hom
        (inclusion R (M ⊗ N) i (m ⊗ₜ[R.obj i] n)) =
      inclusion R M i m ⊗ₜ[ringPoint R] inclusion R N i n := by
  have h := ConcreteCategory.congr_hom
    ((extendedCoconeIsColimit R (M ⊗ N)).comp_coconePointUniqueUpToIso_hom
      (tensorCoconeIsColimit R M N) i)
    (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n))
  change (tensorIso R M N).hom
      (extendedLeg R (M ⊗ N) i
        (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n))) =
    (tensorCocone R M N).ι.app i
      (extendedUnit R (M ⊗ N) i (m ⊗ₜ[R.obj i] n)) at h
  rw [extendedLeg_unit, tensorCocone_ι_unit_tmul] at h
  exact h

private lemma tensorIso_hom_inclusion_tmul_ring
    (i : Cᵒᵖ) (m : M.obj i) (n : N.obj i) :
    (tensorIso R M N).hom
        (inclusion R (M ⊗ N) i
          (m ⊗ₜ[(ringDiagram R).obj i] n)) =
      inclusion R M i m ⊗ₜ[ringPoint R] inclusion R N i n := by
  exact tensorIso_hom_inclusion_tmul R M N i m n

private abbrev additiveMap
    {Q Q' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : Q ⟶ Q') :
    Q.presheaf ⟶ Q'.presheaf :=
  (PresheafOfModules.toPresheaf
    (R ⋙ forget₂ CommRingCat RingCat)).map f

private noncomputable def rawColimitMap
    {Q Q' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : Q ⟶ Q') :
    (modulePoint R Q : Ab.{u}) ⟶ modulePoint R Q' :=
  colim.map (additiveMap R f)

@[simp]
private lemma rawColimitMap_inclusion
    {Q Q' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : Q ⟶ Q')
    (i : Cᵒᵖ) (m : Q.obj i) :
    rawColimitMap R f (inclusion R Q i m) =
      inclusion R Q' i (f.app i m) := by
  have h := ConcreteCategory.congr_hom
    (colimit.ι_map (additiveMap R f) i) m
  change rawColimitMap R f (inclusion R Q i m) =
    inclusion R Q' i (f.app i m) at h
  exact h

/-- A morphism of varying-base module diagrams induces a linear map between
their colimit modules. -/
noncomputable def colimitMap
    {Q Q' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : Q ⟶ Q') :
    colimitObj R Q ⟶ colimitObj R Q' :=
  ModuleCat.ofHom
    { toFun := rawColimitMap R f
      map_add' := fun m n ↦ map_add (rawColimitMap R f).hom m n
      map_smul' := fun r m ↦ by
        obtain ⟨i, a, p, ha, hp⟩ := jointly_surjective R Q r m
        rw [← ha, ← hp, ← inclusion_smul R Q i a p,
          rawColimitMap_inclusion, (f.app i).hom.map_smul,
          inclusion_smul, rawColimitMap_inclusion]
        rw [RingHom.id_apply] }

/-- Formula for the induced colimit map on a local representative. -/
@[simp]
lemma colimitMap_inclusion
    {Q Q' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)} (f : Q ⟶ Q')
    (i : Cᵒᵖ) (m : Q.obj i) :
    colimitMap R f (inclusion R Q i m) =
      inclusion R Q' i (f.app i m) :=
  rawColimitMap_inclusion R f i m

omit [IsFiltered Cᵒᵖ] in
private lemma tensorHom_app_tmul
    {M M' N N' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') (i : Cᵒᵖ)
    (m : M.obj i) (n : N.obj i) :
    (f ⊗ₘ g).app i
        (show (M ⊗ N).obj i from
          m ⊗ₜ[(ringDiagram R).obj i] n) =
      (show (M' ⊗ N').obj i from
        f.app i m ⊗ₜ[(ringDiagram R).obj i] g.app i n) := by
  exact ModuleCat.MonoidalCategory.tensorHom_tmul
    (R := (ringDiagram R).obj i) (f.app i) (g.app i) m n

/-- The filtered-colimit tensor comparison is natural in both module
diagrams. -/
lemma tensorIso_naturality
    {M M' N N' : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    colimitMap R (f ⊗ₘ g) ≫ (tensorIso R M' N').hom =
      (tensorIso R M N).hom ≫
        (colimitMap R f ⊗ₘ colimitMap R g) := by
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨i, z, rfl⟩ := inclusion_jointly_surjective R (M ⊗ N) z
  change (tensorIso R M' N').hom
      (colimitMap R (f ⊗ₘ g) (inclusion R (M ⊗ N) i z)) =
    (colimitMap R f ⊗ₘ colimitMap R g)
      ((tensorIso R M N).hom (inclusion R (M ⊗ N) i z))
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [inclusion_zero, map_zero]
  | tmul m n =>
      rw [colimitMap_inclusion]
      rw [tensorHom_app_tmul, tensorIso_hom_inclusion_tmul_ring,
        tensorIso_hom_inclusion_tmul_ring,
        ModuleCat.MonoidalCategory.tensorHom_tmul,
        colimitMap_inclusion, colimitMap_inclusion]
  | add x y hx hy =>
      rw [inclusion_add R (M ⊗ N) i x y]
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

end

end LSZ.FilteredColimitTensor
