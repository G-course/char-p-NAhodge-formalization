import LSZ.ExtensionScalarsTensor
import LSZ.InverseImagePresheaf

/-!
# Inverse image and tensor products

We first construct, on every open set, the canonical comparison from the
inverse image of an objectwise tensor product to the tensor product of the two
inverse images.  Its invertibility is proved separately below from filtered
colimits and extension of scalars.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open scoped MonoidalCategory TensorProduct

namespace LSZ.InverseImageTensor

universe u

noncomputable section

attribute [local instance] IsFiltered.isSifted
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (A : Y.Presheaf CommRingCat.{u})
  (M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))

private abbrev P (U : (Opens X)ᵒᵖ) :=
  CostructuredArrow.proj (Opens.map f).op U

private noncomputable def sectionObj
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) :
    ModuleCat (InverseImagePresheaf.commRingCocone f A U).pt := by
  letI : Module (InverseImagePresheaf.commRingCocone f A U).pt
      (InverseImagePresheaf.moduleCocone f A Q U).pt := by
    change Module
      ((InverseImagePresheaf.ring f A ⋙
        forget₂ CommRingCat RingCat).obj U)
      ((InverseImagePresheaf.additive f A Q).obj U)
    exact InverseImagePresheaf.sectionModule f A Q U
  exact ModuleCat.of _ (InverseImagePresheaf.moduleCocone f A Q U).pt

private noncomputable abbrev target (U : (Opens X)ᵒᵖ) :
    ModuleCat (InverseImagePresheaf.commRingCocone f A U).pt :=
  sectionObj f A M U ⊗ sectionObj f A N U

private def inclusion
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (m : Q.obj ((P f U).obj j)) : sectionObj f A Q U :=
  (InverseImagePresheaf.moduleCocone f A Q U).ι.app j m

private def ringInclusion (U : (Opens X)ᵒᵖ)
    (j : InverseImagePresheaf.Index f U)
    (a : A.obj ((P f U).obj j)) :
    (InverseImagePresheaf.commRingCocone f A U).pt :=
  (InverseImagePresheaf.commRingCocone f A U).ι.app j a

private lemma section_jointly_surjective
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ)
    (r : (InverseImagePresheaf.commRingCocone f A U).pt)
    (m : sectionObj f A Q U) :
    ∃ (j : InverseImagePresheaf.Index f U)
      (a : A.obj ((P f U).obj j)) (p : Q.obj ((P f U).obj j)),
      ringInclusion f A U j a = r ∧ inclusion f A Q U j p = m := by
  obtain ⟨j, a, p, ha, hp⟩ :=
    InverseImagePresheaf.jointly_surjective f A Q U r m
  refine ⟨j, a, p, ?_, ?_⟩
  · change (InverseImagePresheaf.ringCocone f A U).ι.app j a = r
    exact ha
  · exact hp

private lemma cocone_ι_smul
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (a : A.obj ((P f U).obj j)) (m : Q.obj ((P f U).obj j)) :
    inclusion f A Q U j (a • m) =
      ringInclusion f A U j a • inclusion f A Q U j m := by
  letI (i : InverseImagePresheaf.Index f U) :
      Module ((InverseImagePresheaf.ringDiagram f A U).obj i)
        ((InverseImagePresheaf.moduleDiagram f A Q U).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj ((P f U).obj i))
      (Q.obj ((P f U).obj i))
    infer_instance
  letI : Module (InverseImagePresheaf.commRingCocone f A U).pt
      (InverseImagePresheaf.moduleCocone f A Q U).pt :=
    (sectionObj f A Q U).isModule
  have h := Limits.IsColimit.ι_smul
      (InverseImagePresheaf.ringDiagram f A U)
      (InverseImagePresheaf.moduleDiagram f A Q U)
      (fun q r x ↦ Q.map_smul
        (CostructuredArrow.proj (Opens.map f).op U |>.map q) r x)
      (InverseImagePresheaf.ringIsColimit f A U)
      (InverseImagePresheaf.moduleIsColimit f A Q U) j a m
  change inclusion f A Q U j (a • m) =
    ringInclusion f A U j a • inclusion f A Q U j m at h
  exact h

private abbrev localBase (U : (Opens X)ᵒᵖ) :
    (InverseImagePresheaf.Index f U)ᵒᵖ ⥤ Opens Y :=
  (P f U).leftOp

private abbrev localRing (U : (Opens X)ᵒᵖ) :
    ((InverseImagePresheaf.Index f U)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  (localBase f U).op ⋙ A

private noncomputable abbrev localModule
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) :
    PresheafOfModules.{u}
      (localRing f A U ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward₀OfCommRingCat (localBase f U) A).obj Q

private def toLocalSection
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    (localModule f A Q U).obj
      ((opOp (InverseImagePresheaf.Index f U)).obj j) := by
  exact p

private def fromLocalSection
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p : (localModule f A Q U).obj
      ((opOp (InverseImagePresheaf.Index f U)).obj j)) :
    Q.obj ((P f U).obj j) := by
  exact p

private def fromLocalScalar (U : (Opens X)ᵒᵖ)
    (j : InverseImagePresheaf.Index f U)
    (r : (localRing f A U).obj
      ((opOp (InverseImagePresheaf.Index f U)).obj j)) :
    A.obj ((P f U).obj j) := by
  exact r

private def toLocalScalar (U : (Opens X)ᵒᵖ)
    (j : InverseImagePresheaf.Index f U)
    (r : A.obj ((P f U).obj j)) :
    (localRing f A U).obj
      ((opOp (InverseImagePresheaf.Index f U)).obj j) := by
  exact r

private abbrev localRingCocone (U : (Opens X)ᵒᵖ) :
    Cocone (localRing f A U) := by
  exact Cocone.whisker
    (unopUnop (InverseImagePresheaf.Index f U))
    (InverseImagePresheaf.commRingCocone f A U)

private abbrev constantRing (U : (Opens X)ᵒᵖ) :
    ((InverseImagePresheaf.Index f U)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (InverseImagePresheaf.commRingCocone f A U).pt

private abbrev localRingMap (U : (Opens X)ᵒᵖ) :
    localRing f A U ⟶ constantRing f A U :=
  (localRingCocone f A U).ι

private noncomputable abbrev extendedPresheaf
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) :
    PresheafOfModules.{u}
      (constantRing f A U ⋙ forget₂ CommRingCat RingCat) :=
  CommRingSheaf.extensionPresheaf
    (localRingMap f A U) (localModule f A Q U)

private noncomputable abbrev extendedObj
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U) :=
  (extendedPresheaf f A Q U).obj
    ((opOp (InverseImagePresheaf.Index f U)).obj j)

private noncomputable abbrev extendedMap
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) {i j : InverseImagePresheaf.Index f U}
    (e : i ⟶ j) : extendedObj f A Q U i ⟶ extendedObj f A Q U j :=
  ModuleCat.ofHom
    { toFun := fun (x : extendedObj f A Q U i) ↦
        show extendedObj f A Q U j from
          (extendedPresheaf f A Q U).presheaf.map
            ((opOp (InverseImagePresheaf.Index f U)).map e) x
      map_add' := fun x y ↦ by
        change (extendedPresheaf f A Q U).presheaf.map
            ((opOp (InverseImagePresheaf.Index f U)).map e) (x + y) =
          (extendedPresheaf f A Q U).presheaf.map
              ((opOp (InverseImagePresheaf.Index f U)).map e) x +
            (extendedPresheaf f A Q U).presheaf.map
              ((opOp (InverseImagePresheaf.Index f U)).map e) y
        exact map_add
          ((extendedPresheaf f A Q U).presheaf.map
            ((opOp (InverseImagePresheaf.Index f U)).map e)).hom x y
      map_smul' := fun r x ↦ by
        change (extendedPresheaf f A Q U).map
            ((opOp (InverseImagePresheaf.Index f U)).map e) (r • x) = _
        rw [(extendedPresheaf f A Q U).map_smul]
        rfl }

/-- At a fixed open set, extend every varying-base module to the single
colimit ring.  The maps come from the already constructed objectwise
extension-of-scalars presheaf. -/
noncomputable def extendedDiagram
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) :
    InverseImagePresheaf.Index f U ⥤
      ModuleCat (InverseImagePresheaf.commRingCocone f A U).pt where
  obj j := extendedObj f A Q U j
  map e := extendedMap f A Q U e
  map_id j := by
    apply (forget₂ (ModuleCat
      (InverseImagePresheaf.commRingCocone f A U).pt) Ab).map_injective
    change (extendedPresheaf f A Q U).presheaf.map
        ((opOp (InverseImagePresheaf.Index f U)).map (𝟙 j)) = 𝟙 _
    simp
  map_comp e g := by
    apply (forget₂ (ModuleCat
      (InverseImagePresheaf.commRingCocone f A U).pt) Ab).map_injective
    change (extendedPresheaf f A Q U).presheaf.map
        ((opOp (InverseImagePresheaf.Index f U)).map (e ≫ g)) =
      (extendedPresheaf f A Q U).presheaf.map
          ((opOp (InverseImagePresheaf.Index f U)).map e) ≫
        (extendedPresheaf f A Q U).presheaf.map
          ((opOp (InverseImagePresheaf.Index f U)).map g)
    simp

/-- The standard generator `1 ⊗ p` in the extended local diagram. -/
def extendedUnit
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) : (extendedDiagram f A Q U).obj j :=
  CommRingSheaf.extensionUnit (localRingMap f A U)
    (localModule f A Q U)
    ((opOp (InverseImagePresheaf.Index f U)).obj j)
      (toLocalSection f A Q U j p)

@[simp]
lemma extendedUnit_add
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p q : Q.obj ((P f U).obj j)) :
    extendedUnit f A Q U j (p + q) =
      extendedUnit f A Q U j p + extendedUnit f A Q U j q := by
  have h := CommRingSheaf.extensionUnit_add
    (localRingMap f A U) (localModule f A Q U)
    ((opOp (InverseImagePresheaf.Index f U)).obj j)
    (toLocalSection f A Q U j p) (toLocalSection f A Q U j q)
  change extendedUnit f A Q U j (p + q) =
    extendedUnit f A Q U j p + extendedUnit f A Q U j q at h
  exact h

@[simp]
lemma extendedUnit_smul
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (a : A.obj ((P f U).obj j)) (p : Q.obj ((P f U).obj j)) :
    extendedUnit f A Q U j (a • p) =
      ringInclusion f A U j a • extendedUnit f A Q U j p := by
  have h := CommRingSheaf.extensionUnit_smul
    (localRingMap f A U) (localModule f A Q U)
    ((opOp (InverseImagePresheaf.Index f U)).obj j)
    (toLocalScalar f A U j a) (toLocalSection f A Q U j p)
  change extendedUnit f A Q U j (a • p) =
    ringInclusion f A U j a • extendedUnit f A Q U j p at h
  exact h

private noncomputable def inclusionLinear
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U) :
    (localModule f A Q U).obj
        ((opOp (InverseImagePresheaf.Index f U)).obj j) ⟶
      (ModuleCat.restrictScalars
        ((localRingMap f A U).app
          ((opOp (InverseImagePresheaf.Index f U)).obj j)).hom).obj
        (sectionObj f A Q U) :=
  ModuleCat.ofHom
    (X := (localModule f A Q U).obj
      ((opOp (InverseImagePresheaf.Index f U)).obj j))
    (Y := (ModuleCat.restrictScalars
      ((localRingMap f A U).app
        ((opOp (InverseImagePresheaf.Index f U)).obj j)).hom).obj
      (sectionObj f A Q U))
    { toFun := fun x ↦ show
          (ModuleCat.restrictScalars
            ((localRingMap f A U).app
              ((opOp (InverseImagePresheaf.Index f U)).obj j)).hom).obj
            (sectionObj f A Q U) from
        inclusion f A Q U j (fromLocalSection f A Q U j x)
      map_add' := fun x y ↦ by
        change inclusion f A Q U j
            (fromLocalSection f A Q U j (x + y)) =
          inclusion f A Q U j (fromLocalSection f A Q U j x) +
            inclusion f A Q U j (fromLocalSection f A Q U j y)
        exact ((InverseImagePresheaf.moduleCocone f A Q U).ι.app j).hom.map_add _ _
      map_smul' := fun r x ↦ by
        change inclusion f A Q U j
            (fromLocalScalar f A U j r •
              fromLocalSection f A Q U j x) =
          ringInclusion f A U j (fromLocalScalar f A U j r) •
            inclusion f A Q U j (fromLocalSection f A Q U j x)
        exact cocone_ι_smul f A Q U j _ _ }

/-- The canonical leg `R_U ⊗[A_j] Q_j → (f⁻¹Q)(U)`. -/
noncomputable def extendedSectionLeg
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U) :
    (extendedDiagram f A Q U).obj j ⟶ sectionObj f A Q U :=
  ((ModuleCat.extendRestrictScalarsAdj
    ((localRingMap f A U).app
      ((opOp (InverseImagePresheaf.Index f U)).obj j)).hom).homEquiv _ _).symm
        (inclusionLinear f A Q U j)

@[simp]
lemma extendedSectionLeg_unit
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    extendedSectionLeg f A Q U j (extendedUnit f A Q U j p) =
      inclusion f A Q U j p := by
  change ((ModuleCat.extendRestrictScalarsAdj
      ((localRingMap f A U).app
        ((opOp (InverseImagePresheaf.Index f U)).obj j)).hom).homEquiv _ _).symm
        (inclusionLinear f A Q U j)
          (CommRingSheaf.extensionUnit (localRingMap f A U)
            (localModule f A Q U)
            ((opOp (InverseImagePresheaf.Index f U)).obj j)
              (toLocalSection f A Q U j p)) = _
  calc
    _ = inclusionLinear f A Q U j (toLocalSection f A Q U j p) :=
      CommRingSheaf.extensionHomEquiv_symm_unit
        (localRingMap f A U) (localModule f A Q U)
        (sectionObj f A Q U) (inclusionLinear f A Q U j)
        (toLocalSection f A Q U j p)
    _ = inclusion f A Q U j p := rfl

@[simp]
lemma extendedDiagram_map_unit
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) {i j : InverseImagePresheaf.Index f U}
    (e : i ⟶ j) (p : Q.obj ((P f U).obj i)) :
    (extendedDiagram f A Q U).map e (extendedUnit f A Q U i p) =
      extendedUnit f A Q U j (Q.map ((P f U).map e) p) := by
  have h := CommRingSheaf.extensionPresheafMap_unit
    (localRingMap f A U) (localModule f A Q U)
    ((opOp (InverseImagePresheaf.Index f U)).map e)
    (toLocalSection f A Q U i p)
  change (extendedDiagram f A Q U).map e
      (extendedUnit f A Q U i p) =
    extendedUnit f A Q U j (Q.map ((P f U).map e) p) at h
  exact h

/-- The extended local modules map to the original Kan colimit by
`r ⊗ p ↦ r • ι(p)`.  This definition uses only the extension-of-scalars
universal property; filteredness does not enter the map itself. -/
noncomputable def extendedSectionCocone
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) : Cocone (extendedDiagram f A Q U) where
  pt := sectionObj f A Q U
  ι :=
    { app := extendedSectionLeg f A Q U
      naturality := by
        intro i j e
        apply CommRingSheaf.extensionHom_ext
          (localRingMap f A U) (localModule f A Q U)
          ((opOp (InverseImagePresheaf.Index f U)).obj i)
        intro p
        let p' := fromLocalSection f A Q U i p
        change extendedSectionLeg f A Q U j
            ((extendedDiagram f A Q U).map e
              (extendedUnit f A Q U i p')) =
          extendedSectionLeg f A Q U i
            (extendedUnit f A Q U i p')
        rw [extendedDiagram_map_unit, extendedSectionLeg_unit,
          extendedSectionLeg_unit]
        have h := ConcreteCategory.congr_hom
          ((InverseImagePresheaf.moduleCocone f A Q U).w e) p'
        change inclusion f A Q U j (Q.map ((P f U).map e) p') =
          inclusion f A Q U i p' at h
        exact h }

private noncomputable def generatorCocone
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (s : Cocone (extendedDiagram f A Q U)) :
    Cocone (InverseImagePresheaf.moduleDiagram f A Q U) where
  pt := (forget₂ (ModuleCat
    (InverseImagePresheaf.commRingCocone f A U).pt) Ab).obj s.pt
  ι :=
    { app := fun j ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun p ↦ s.ι.app j (extendedUnit f A Q U j p))
        (fun p q ↦ by
          rw [extendedUnit_add]
          exact map_add (s.ι.app j).hom _ _)
      naturality := by
        intro i j e
        apply (forget Ab).map_injective
        ext p
        have h := ConcreteCategory.congr_hom (s.w e)
          (extendedUnit f A Q U i p)
        change s.ι.app j
            ((extendedDiagram f A Q U).map e
              (extendedUnit f A Q U i p)) =
          s.ι.app i (extendedUnit f A Q U i p) at h
        rw [extendedDiagram_map_unit] at h
        exact h }

private noncomputable def generatorDesc
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (s : Cocone (extendedDiagram f A Q U)) :
    (InverseImagePresheaf.moduleCocone f A Q U).pt ⟶
      (forget₂ (ModuleCat
        (InverseImagePresheaf.commRingCocone f A U).pt) Ab).obj s.pt :=
  (InverseImagePresheaf.moduleIsColimit f A Q U).desc
    (generatorCocone f A Q U s)

@[simp]
private lemma generatorDesc_inclusion
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (s : Cocone (extendedDiagram f A Q U))
    (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    generatorDesc f A Q U s (inclusion f A Q U j p) =
      s.ι.app j (extendedUnit f A Q U j p) := by
  have h := ConcreteCategory.congr_hom
    ((InverseImagePresheaf.moduleIsColimit f A Q U).fac
      (generatorCocone f A Q U s) j) p
  change generatorDesc f A Q U s (inclusion f A Q U j p) =
    s.ι.app j (extendedUnit f A Q U j p) at h
  exact h

private noncomputable def extendedSectionDesc
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (s : Cocone (extendedDiagram f A Q U)) :
    sectionObj f A Q U ⟶ s.pt :=
  ModuleCat.ofHom (X := sectionObj f A Q U) (Y := s.pt)
    { toFun := fun m ↦ generatorDesc f A Q U s m
      map_add' := fun m n ↦ (generatorDesc f A Q U s).hom.map_add m n
      map_smul' := fun r m ↦ by
        obtain ⟨j, a, p, ha, hp⟩ :=
          section_jointly_surjective f A Q U r m
        rw [← ha, ← hp]
        change generatorDesc f A Q U s
            (ringInclusion f A U j a • inclusion f A Q U j p) =
          ringInclusion f A U j a •
            (show s.pt from
              generatorDesc f A Q U s (inclusion f A Q U j p))
        rw [← cocone_ι_smul f A Q U j a p,
          generatorDesc_inclusion, generatorDesc_inclusion,
          extendedUnit_smul]
        exact map_smul (s.ι.app j).hom _ _ }

@[simp]
private lemma extendedSectionDesc_inclusion
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (s : Cocone (extendedDiagram f A Q U))
    (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    extendedSectionDesc f A Q U s (inclusion f A Q U j p) =
      s.ι.app j (extendedUnit f A Q U j p) :=
  generatorDesc_inclusion f A Q U s j p

private lemma inclusion_jointly_surjective
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (m : sectionObj f A Q U) :
    ∃ (j : InverseImagePresheaf.Index f U)
      (p : Q.obj ((P f U).obj j)), inclusion f A Q U j p = m := by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget Ab)
      (InverseImagePresheaf.moduleIsColimit f A Q U)) m
  exact ⟨j, p, hp⟩

private lemma module_inclusion_jointly_surjective
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (m : (InverseImagePresheaf.module f A Q).obj U) :
    ∃ (j : InverseImagePresheaf.Index f U)
      (p : Q.obj ((P f U).obj j)), inclusion f A Q U j p = m := by
  obtain ⟨j, p, hp⟩ :=
    InverseImagePresheaf.module_jointly_surjective f A Q U m
  refine ⟨j, p, ?_⟩
  exact hp

/-- The fixed-open cocone of extended modules has as colimit the same
`sectionModule` used by the inverse-image presheaf. -/
noncomputable def extendedSectionCocone_isColimit
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) :
    IsColimit (extendedSectionCocone f A Q U) :=
  IsColimit.mk
    (fun s ↦ extendedSectionDesc f A Q U s)
    (fun s j ↦ by
      apply CommRingSheaf.extensionHom_ext
        (localRingMap f A U) (localModule f A Q U)
        ((opOp (InverseImagePresheaf.Index f U)).obj j)
      intro p
      let p' := fromLocalSection f A Q U j p
      change extendedSectionDesc f A Q U s
          (extendedSectionLeg f A Q U j
            (extendedUnit f A Q U j p')) =
        s.ι.app j (extendedUnit f A Q U j p')
      rw [extendedSectionLeg_unit, extendedSectionDesc_inclusion])
    (fun s m hm ↦ by
      apply ModuleCat.hom_ext
      ext x
      obtain ⟨j, p, rfl⟩ := inclusion_jointly_surjective f A Q U x
      have h := ConcreteCategory.congr_hom (hm j)
        (extendedUnit f A Q U j p)
      change m (extendedSectionLeg f A Q U j
          (extendedUnit f A Q U j p)) =
        s.ι.app j (extendedUnit f A Q U j p) at h
      rw [extendedSectionLeg_unit] at h
      exact h.trans (extendedSectionDesc_inclusion f A Q U s j p).symm)

/-- Extension of scalars distributes over tensor product at one index of the
fixed-open diagram. -/
noncomputable def extendedTensorSectionIso
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U) :
    (extendedDiagram f A (M ⊗ N) U).obj j ≅
      ((extendedDiagram f A M U) ⊗ (extendedDiagram f A N U)).obj j :=
  CommRingSheaf.extensionTensorSectionIso
    (localRingMap f A U) (localModule f A M U) (localModule f A N U)
    ((opOp (InverseImagePresheaf.Index f U)).obj j)

set_option maxHeartbeats 1000000 in
private lemma extendedTensorSectionIso_naturality
    (U : (Opens X)ᵒᵖ) {i j : InverseImagePresheaf.Index f U}
    (e : i ⟶ j) :
    (extendedDiagram f A (M ⊗ N) U).map e ≫
        (extendedTensorSectionIso f A M N U j).hom =
      (extendedTensorSectionIso f A M N U i).hom ≫
        ((extendedDiagram f A M U) ⊗
          (extendedDiagram f A N U)).map e := by
  have h := (CommRingSheaf.extensionTensorPresheafIso
    (localRingMap f A U) (localModule f A M U)
      (localModule f A N U)).hom.naturality
        ((opOp (InverseImagePresheaf.Index f U)).map e)
  change (extendedDiagram f A (M ⊗ N) U).map e ≫
      (extendedTensorSectionIso f A M N U j).hom =
    (extendedTensorSectionIso f A M N U i).hom ≫
      ((extendedDiagram f A M U) ⊗
        (extendedDiagram f A N U)).map e at h
  exact h

/-- Diagramwise extension of scalars distributes over tensor product.  The
components and their naturality are defined and proved separately above. -/
noncomputable def extendedTensorDiagramIso (U : (Opens X)ᵒᵖ) :
    extendedDiagram f A (M ⊗ N) U ≅
      extendedDiagram f A M U ⊗ extendedDiagram f A N U :=
  NatIso.ofComponents (extendedTensorSectionIso f A M N U)
    (extendedTensorSectionIso_naturality f A M N U)

@[simp]
lemma extendedTensorSectionIso_hom_unit_tmul
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    (extendedTensorSectionIso f A M N U j).hom
        (extendedUnit f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n)) =
      extendedUnit f A M U j m ⊗ₜ[
        (InverseImagePresheaf.commRingCocone f A U).pt]
          extendedUnit f A N U j n := by
  have h := CommRingSheaf.extensionTensorSectionIso_hom_unit_tmul
    (localRingMap f A U) (localModule f A M U) (localModule f A N U)
    ((opOp (InverseImagePresheaf.Index f U)).obj j)
    (toLocalSection f A M U j m) (toLocalSection f A N U j n)
  change (extendedTensorSectionIso f A M N U j).hom
      (extendedUnit f A (M ⊗ N) U j
        (m ⊗ₜ[A.obj ((P f U).obj j)] n)) =
    extendedUnit f A M U j m ⊗ₜ[
      (InverseImagePresheaf.commRingCocone f A U).pt]
        extendedUnit f A N U j n at h
  exact h

private noncomputable def tensorSectionCocone (U : (Opens X)ᵒᵖ) :
    Cocone (extendedDiagram f A (M ⊗ N) U) :=
  (Cocone.precompose (extendedTensorDiagramIso f A M N U).hom).obj
    ((extendedSectionCocone f A M U).tensor
      (extendedSectionCocone f A N U))

private noncomputable def tensorSectionCocone_isColimit
    (U : (Opens X)ᵒᵖ) : IsColimit (tensorSectionCocone f A M N U) :=
  (IsColimit.precomposeHomEquiv (extendedTensorDiagramIso f A M N U)
    ((extendedSectionCocone f A M U).tensor
      (extendedSectionCocone f A N U))).symm
        ((extendedSectionCocone_isColimit f A M U).tensor
          (extendedSectionCocone_isColimit f A N U))

/-- The fixed-open tensor comparison, obtained only after proving both
cocones colimiting. -/
noncomputable def sectionTensorIso (U : (Opens X)ᵒᵖ) :
    sectionObj f A (M ⊗ N) U ≅ target f A M N U :=
  (extendedSectionCocone_isColimit f A (M ⊗ N) U).coconePointUniqueUpToIso
    (tensorSectionCocone_isColimit f A M N U)

@[simp]
private lemma tensorSectionCocone_ι_unit_tmul
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    (tensorSectionCocone f A M N U).ι.app j
        (extendedUnit f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n)) =
      inclusion f A M U j m ⊗ₜ[
        (InverseImagePresheaf.commRingCocone f A U).pt]
          inclusion f A N U j n := by
  change ((extendedSectionLeg f A M U j) ⊗ₘ
      (extendedSectionLeg f A N U j))
        ((extendedTensorSectionIso f A M N U j).hom
          (extendedUnit f A (M ⊗ N) U j
            (m ⊗ₜ[A.obj ((P f U).obj j)] n))) = _
  rw [extendedTensorSectionIso_hom_unit_tmul,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    extendedSectionLeg_unit, extendedSectionLeg_unit]

@[simp]
lemma sectionTensorIso_hom_inclusion_tmul
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    (sectionTensorIso f A M N U).hom
        (inclusion f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n)) =
      inclusion f A M U j m ⊗ₜ[
        (InverseImagePresheaf.commRingCocone f A U).pt]
          inclusion f A N U j n := by
  have h := ConcreteCategory.congr_hom
    ((extendedSectionCocone_isColimit f A (M ⊗ N) U).comp_coconePointUniqueUpToIso_hom
        (tensorSectionCocone_isColimit f A M N U) j)
    (extendedUnit f A (M ⊗ N) U j
      (m ⊗ₜ[A.obj ((P f U).obj j)] n))
  change (sectionTensorIso f A M N U).hom
      (extendedSectionLeg f A (M ⊗ N) U j
        (extendedUnit f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n))) =
    (tensorSectionCocone f A M N U).ι.app j
      (extendedUnit f A (M ⊗ N) U j
        (m ⊗ₜ[A.obj ((P f U).obj j)] n)) at h
  rw [extendedSectionLeg_unit, tensorSectionCocone_ι_unit_tmul] at h
  exact h

/-- The sectionwise comparison written with the actual inverse-image
presheaves. -/
noncomputable def tensorIsoApp (U : (Opens X)ᵒᵖ) :
    (InverseImagePresheaf.module f A (M ⊗ N)).obj U ≅
      ((InverseImagePresheaf.module f A M) ⊗
        (InverseImagePresheaf.module f A N)).obj U :=
  sectionTensorIso f A M N U

@[simp]
private lemma inverseImage_map_inclusion
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    (InverseImagePresheaf.module f A Q).map q
        (inclusion f A Q U j p) =
      inclusion f A Q V ((CostructuredArrow.map q).obj j) p := by
  have h := InverseImagePresheaf.map_module_cocone_apply f A Q q j p
  change (InverseImagePresheaf.module f A Q).map q
      (inclusion f A Q U j p) =
    inclusion f A Q V ((CostructuredArrow.map q).obj j) p at h
  exact h

@[simp]
private lemma moduleMap_inclusion
    {Q Q' : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : Q ⟶ Q') (U : (Opens X)ᵒᵖ)
    (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    (InverseImagePresheaf.moduleMap f A g).app U
        (inclusion f A Q U j p) =
      inclusion f A Q' U j (g.app ((P f U).obj j) p) := by
  have h := InverseImagePresheaf.moduleMap_cocone_apply f A g U j p
  change (InverseImagePresheaf.moduleMap f A g).app U
      (inclusion f A Q U j p) =
    inclusion f A Q' U j (g.app ((P f U).obj j) p) at h
  exact h

@[simp]
private lemma inclusion_zero
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U) :
    inclusion f A Q U j 0 = 0 :=
  map_zero ((InverseImagePresheaf.moduleCocone f A Q U).ι.app j).hom

@[simp]
private lemma inclusion_add
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (p q : Q.obj ((P f U).obj j)) :
    inclusion f A Q U j (p + q) =
      inclusion f A Q U j p + inclusion f A Q U j q :=
  map_add ((InverseImagePresheaf.moduleCocone f A Q U).ι.app j).hom p q

private def atMappedIndex
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : InverseImagePresheaf.Index f U)
    (p : Q.obj ((P f U).obj j)) :
    Q.obj ((P f V).obj ((CostructuredArrow.map q).obj j)) := by
  exact p

private lemma atMappedIndex_tmul
    {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    atMappedIndex f A (M ⊗ N) q j
        (m ⊗ₜ[A.obj ((P f U).obj j)] n) =
      atMappedIndex f A M q j m ⊗ₜ[
        A.obj ((P f V).obj ((CostructuredArrow.map q).obj j))]
          atMappedIndex f A N q j n := by
  rfl

private lemma inverseImage_tensor_map_inclusion_tmul
    {U V : (Opens X)ᵒᵖ} (q : U ⟶ V)
    (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    ((InverseImagePresheaf.module f A M) ⊗
      (InverseImagePresheaf.module f A N)).map q
        (show ((InverseImagePresheaf.module f A M) ⊗
          (InverseImagePresheaf.module f A N)).obj U from
          inclusion f A M U j m ⊗ₜ[
            (InverseImagePresheaf.commRingCocone f A U).pt]
              inclusion f A N U j n) =
      (show ((InverseImagePresheaf.module f A M) ⊗
        (InverseImagePresheaf.module f A N)).obj V from
        inclusion f A M V ((CostructuredArrow.map q).obj j)
            (atMappedIndex f A M q j m) ⊗ₜ[
          (InverseImagePresheaf.commRingCocone f A V).pt]
            inclusion f A N V ((CostructuredArrow.map q).obj j)
              (atMappedIndex f A N q j n)) := by
  have h := PresheafOfModules.Monoidal.tensorObj_map_tmul
    (M₁ := InverseImagePresheaf.module f A M)
    (M₂ := InverseImagePresheaf.module f A N) q
    (show (InverseImagePresheaf.module f A M).obj U from
      inclusion f A M U j m)
    (show (InverseImagePresheaf.module f A N).obj U from
      inclusion f A N U j n)
  rw [inverseImage_map_inclusion, inverseImage_map_inclusion] at h
  change ((InverseImagePresheaf.module f A M) ⊗
      (InverseImagePresheaf.module f A N)).map q
        (show ((InverseImagePresheaf.module f A M) ⊗
          (InverseImagePresheaf.module f A N)).obj U from
          inclusion f A M U j m ⊗ₜ[
            (InverseImagePresheaf.commRingCocone f A U).pt]
              inclusion f A N U j n) =
    (show ((InverseImagePresheaf.module f A M) ⊗
      (InverseImagePresheaf.module f A N)).obj V from
      inclusion f A M V ((CostructuredArrow.map q).obj j)
          (atMappedIndex f A M q j m) ⊗ₜ[
        (InverseImagePresheaf.commRingCocone f A V).pt]
          inclusion f A N V ((CostructuredArrow.map q).obj j)
            (atMappedIndex f A N q j n)) at h
  exact h

private lemma tensorIsoApp_naturality
    {U V : (Opens X)ᵒᵖ} (q : U ⟶ V) :
    (InverseImagePresheaf.module f A (M ⊗ N)).map q ≫
        (ModuleCat.restrictScalars
          ((InverseImagePresheaf.ring f A ⋙
            forget₂ CommRingCat RingCat).map q).hom).map
          (tensorIsoApp f A M N V).hom =
      (tensorIsoApp f A M N U).hom ≫
        ((InverseImagePresheaf.module f A M) ⊗
          (InverseImagePresheaf.module f A N)).map q := by
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨j, z, rfl⟩ := inclusion_jointly_surjective f A (M ⊗ N) U x
  simp only [CategoryTheory.comp_apply, ModuleCat.restrictScalars.map_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp only [inclusion_zero, map_zero]
  | tmul m n =>
      rw [inverseImage_map_inclusion]
      change (sectionTensorIso f A M N V).hom
          (inclusion f A (M ⊗ N) V ((CostructuredArrow.map q).obj j)
            (atMappedIndex f A (M ⊗ N) q j
              (m ⊗ₜ[A.obj ((P f U).obj j)] n))) =
        ((InverseImagePresheaf.module f A M) ⊗
          (InverseImagePresheaf.module f A N)).map q
            ((sectionTensorIso f A M N U).hom
              (inclusion f A (M ⊗ N) U j
                (m ⊗ₜ[A.obj ((P f U).obj j)] n)))
      rw [atMappedIndex_tmul,
        sectionTensorIso_hom_inclusion_tmul,
        sectionTensorIso_hom_inclusion_tmul]
      exact (inverseImage_tensor_map_inclusion_tmul f A M N q j m n).symm
  | add z w hz hw =>
      rw [inclusion_add]
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hz hw

/-- Explicit inverse image preserves tensor products at the presheaf level. -/
noncomputable def inverseImageTensorIso :
    InverseImagePresheaf.module f A (M ⊗ N) ≅
      InverseImagePresheaf.module f A M ⊗
        InverseImagePresheaf.module f A N :=
  PresheafOfModules.isoMk (tensorIsoApp f A M N)
    (naturality := by
      intro U V q
      exact tensorIsoApp_naturality f A M N q)

@[simp]
lemma inverseImageTensorIso_hom_app_inclusion_tmul
    (U : (Opens X)ᵒᵖ) (j : InverseImagePresheaf.Index f U)
    (m : M.obj ((P f U).obj j)) (n : N.obj ((P f U).obj j)) :
    (inverseImageTensorIso f A M N).hom.app U
        (inclusion f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n)) =
      inclusion f A M U j m ⊗ₜ[
        (InverseImagePresheaf.commRingCocone f A U).pt]
          inclusion f A N U j n :=
  by
    change (sectionTensorIso f A M N U).hom
        (inclusion f A (M ⊗ N) U j
          (m ⊗ₜ[A.obj ((P f U).obj j)] n)) = _
    exact sectionTensorIso_hom_inclusion_tmul f A M N U j m n

private lemma inverseImageTensorIso_naturality
    {M M' N N' :
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ M') (h : N ⟶ N') :
    InverseImagePresheaf.moduleMap f A (g ⊗ₘ h) ≫
        (inverseImageTensorIso f A M' N').hom =
      (inverseImageTensorIso f A M N).hom ≫
        (InverseImagePresheaf.moduleMap f A g ⊗ₘ
          InverseImagePresheaf.moduleMap f A h) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨j, z, rfl⟩ :=
    module_inclusion_jointly_surjective f A (M ⊗ N) U x
  change (inverseImageTensorIso f A M' N').hom.app U
      ((InverseImagePresheaf.moduleMap f A (g ⊗ₘ h)).app U
        (inclusion f A (M ⊗ N) U j z)) =
    (InverseImagePresheaf.moduleMap f A g ⊗ₘ
      InverseImagePresheaf.moduleMap f A h).app U
        ((inverseImageTensorIso f A M N).hom.app U
          (inclusion f A (M ⊗ N) U j z))
  induction z using TensorProduct.induction_on with
  | zero => simp only [inclusion_zero, map_zero]
  | tmul m n =>
      change (inverseImageTensorIso f A M' N').hom.app U
          ((InverseImagePresheaf.moduleMap f A (g ⊗ₘ h)).app U
            (inclusion f A (M ⊗ N) U j
              (m ⊗ₜ[A.obj ((P f U).obj j)] n))) =
        (InverseImagePresheaf.moduleMap f A g ⊗ₘ
          InverseImagePresheaf.moduleMap f A h).app U
            ((inverseImageTensorIso f A M N).hom.app U
              (inclusion f A (M ⊗ N) U j
                (m ⊗ₜ[A.obj ((P f U).obj j)] n)))
      have hgh := ModuleCat.MonoidalCategory.tensorHom_tmul
        (g.app ((P f U).obj j)) (h.app ((P f U).obj j)) m n
      change (g ⊗ₘ h).app ((P f U).obj j)
          (m ⊗ₜ[A.obj ((P f U).obj j)] n) =
        g.app ((P f U).obj j) m ⊗ₜ[A.obj ((P f U).obj j)]
          h.app ((P f U).obj j) n at hgh
      have hleft :
          (inverseImageTensorIso f A M' N').hom.app U
              ((InverseImagePresheaf.moduleMap f A (g ⊗ₘ h)).app U
                (inclusion f A (M ⊗ N) U j
                  (m ⊗ₜ[A.obj ((P f U).obj j)] n))) =
            inclusion f A M' U j (g.app ((P f U).obj j) m) ⊗ₜ[
              (InverseImagePresheaf.commRingCocone f A U).pt]
              inclusion f A N' U j (h.app ((P f U).obj j) n) := by
        rw [moduleMap_inclusion, hgh,
          inverseImageTensorIso_hom_app_inclusion_tmul]
      have hright :
          (InverseImagePresheaf.moduleMap f A g ⊗ₘ
              InverseImagePresheaf.moduleMap f A h).app U
              (show ((InverseImagePresheaf.module f A M) ⊗
                  (InverseImagePresheaf.module f A N)).obj U from
                inclusion f A M U j m ⊗ₜ[
                  (InverseImagePresheaf.commRingCocone f A U).pt]
                  inclusion f A N U j n) =
            (show ((InverseImagePresheaf.module f A M') ⊗
                (InverseImagePresheaf.module f A N')).obj U from
              inclusion f A M' U j (g.app ((P f U).obj j) m) ⊗ₜ[
                (InverseImagePresheaf.commRingCocone f A U).pt]
                inclusion f A N' U j (h.app ((P f U).obj j) n)) := by
        have hmap := ModuleCat.MonoidalCategory.tensorHom_tmul
          ((InverseImagePresheaf.moduleMap f A g).app U)
          ((InverseImagePresheaf.moduleMap f A h).app U)
          (show (InverseImagePresheaf.module f A M).obj U from
            inclusion f A M U j m)
          (show (InverseImagePresheaf.module f A N).obj U from
            inclusion f A N U j n)
        rw [moduleMap_inclusion, moduleMap_inclusion] at hmap
        change
          (InverseImagePresheaf.moduleMap f A g ⊗ₘ
              InverseImagePresheaf.moduleMap f A h).app U
              (inclusion f A M U j m ⊗ₜ[
                (InverseImagePresheaf.commRingCocone f A U).pt]
                inclusion f A N U j n) =
            inclusion f A M' U j (g.app ((P f U).obj j) m) ⊗ₜ[
              (InverseImagePresheaf.commRingCocone f A U).pt]
              inclusion f A N' U j (h.app ((P f U).obj j) n) at hmap
        exact hmap
      rw [inverseImageTensorIso_hom_app_inclusion_tmul]
      exact hleft.trans hright.symm
  | add z w hz hw =>
      rw [inclusion_add]
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hz hw

private noncomputable abbrev sourceTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)))

private noncomputable abbrev targetTensorBifunctor :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u}
      (InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)))

/-- First tensor, then take explicit inverse image. -/
noncomputable def inverseImageTensorSourceFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u}
        (InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) :=
  sourceTensorBifunctor (A := A) ⋙ InverseImagePresheaf.moduleFunctor f A

/-- First take both explicit inverse images, then tensor. -/
noncomputable def inverseImageTensorTargetFunctor :
    (PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u}
        (InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) :=
  Functor.prod (InverseImagePresheaf.moduleFunctor f A)
      (InverseImagePresheaf.moduleFunctor f A) ⋙
    targetTensorBifunctor f A

private lemma inverseImageTensorNatIso_naturality
    {X Y : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : X ⟶ Y) :
    (inverseImageTensorSourceFunctor f A).map g ≫
        (inverseImageTensorIso f A Y.1 Y.2).hom =
      (inverseImageTensorIso f A X.1 X.2).hom ≫
        (inverseImageTensorTargetFunctor f A).map g := by
  dsimp [inverseImageTensorSourceFunctor, inverseImageTensorTargetFunctor,
    sourceTensorBifunctor, targetTensorBifunctor]
  rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def]
  exact inverseImageTensorIso_naturality f A g.1 g.2

/-- Explicit inverse image is naturally strong monoidal for tensor products. -/
noncomputable def inverseImageTensorNatIso :
    inverseImageTensorSourceFunctor f A ≅
      inverseImageTensorTargetFunctor f A :=
  NatIso.ofComponents
    (fun MN ↦ inverseImageTensorIso f A MN.1 MN.2)
    (inverseImageTensorNatIso_naturality f A)

end

end LSZ.InverseImageTensor
