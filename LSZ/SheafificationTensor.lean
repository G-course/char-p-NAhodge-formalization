import LSZ.StalkTensor
import LSZ.SheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification and tensor products of module presheaves

On a topological space, sheafifying an objectwise tensor product agrees with
tensoring the two sheafifications.  The comparison morphism is defined first;
its invertibility is then proved stalkwise.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open scoped MonoidalCategory TensorProduct

namespace LSZ.SheafificationTensor

universe u

noncomputable section

variable {X : TopCat.{u}}

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance hasSheafCompose :
    (Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ CommRingCat RingCat.{u}) := by
  infer_instance

local instance directRingMap_locallyInjective
    (R : TopCat.Sheaf CommRingCat.{u} X) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CommRingSheaf.directRingMap R) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

local instance directRingMap_locallySurjective
    (R : TopCat.Sheaf CommRingCat.{u} X) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CommRingSheaf.directRingMap R) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

private lemma isLocallyInjective_of_stalk_injective
    {F G : X.Presheaf Ab.{u}} (f : F ⟶ G)
    (hf : ∀ x : X,
      Function.Injective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f := by
  constructor
  intro U s t hst
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have hgerm :
      F.germ U.unop x hx s = F.germ U.unop x hx t := by
    apply hf x
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply, hst]
  obtain ⟨V, hxV, i₁, i₂, hV⟩ :=
    F.germ_eq x hx hx s t hgerm
  refine ⟨V, i₁, ?_, hxV⟩
  change F.map i₁.op s = F.map i₁.op t
  simpa only [Subsingleton.elim i₂ i₁] using hV

/-- The unit from a module presheaf to the underlying presheaf of its
sheafification. -/
noncomputable def unit
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ CommRingSheaf.directPresheaf R
      ((CommRingSheaf.directSheafificationFunctor R).obj P) :=
  (CommRingSheaf.directSheafificationAdjunction R).unit.app P ≫
    CommRingSheaf.unrestrictId R
      ((CommRingSheaf.directSheafificationFunctor R).obj P).val

private lemma toPresheaf_map_unit
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map (unit R P) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        P.presheaf := by
  ext U p
  rfl

private lemma unit_stalk_isIso
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso (StalkTensor.map R.obj x (unit R P)) := by
  rw [← isIso_iff_of_reflects_iso
    (StalkTensor.map R.obj x (unit R P))
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk
      (C := CommRingCat.{u}) R.obj x)) Ab)]
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map (unit R P)))
  rw [toPresheaf_map_unit]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x Ab.{u} P.presheaf

/-- Tensor the two sheafification units before applying sheafification. -/
noncomputable def tensorUnitMap
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⊗ Q ⟶
      CommRingSheaf.directPresheaf R
          ((CommRingSheaf.directSheafificationFunctor R).obj P) ⊗
        CommRingSheaf.directPresheaf R
          ((CommRingSheaf.directSheafificationFunctor R).obj Q) :=
  unit R P ⊗ₘ unit R Q

private lemma tensorUnitMap_stalk_isIso
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso (StalkTensor.map R.obj x (tensorUnitMap R P Q)) := by
  letI := unit_stalk_isIso R P x
  letI := unit_stalk_isIso R Q x
  exact IsIso.of_isIso_fac_right
    (StalkTensor.tensorIso_naturality R.obj x (unit R P) (unit R Q))

private lemma underlying_tensorUnitMap_stalk_isIso
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf
        (R.obj ⋙ forget₂ CommRingCat RingCat)).map
          (tensorUnitMap R P Q))) := by
  letI := tensorUnitMap_stalk_isIso R P Q x
  change IsIso ((forget₂ (ModuleCat (TopCat.Presheaf.stalk
      (C := CommRingCat.{u}) R.obj x)) Ab).map
    (StalkTensor.map R.obj x (tensorUnitMap R P Q)))
  infer_instance

private lemma tensorUnitMap_mem_W
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf
        (R.obj ⋙ forget₂ CommRingCat RingCat)).map
          (tensorUnitMap R P Q)) := by
  rw [(Opens.grothendieckTopology X).W_iff_isLocallyBijective]
  constructor
  · apply isLocallyInjective_of_stalk_injective
    intro x
    letI := underlying_tensorUnitMap_stalk_isIso R P Q x
    exact (bijective_iff_isIso_ofHom _).mpr inferInstance |>.injective
  · let φ := (PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map (tensorUnitMap R P Q)
    change TopCat.Presheaf.IsLocallySurjective φ
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ).2
    intro x
    letI := underlying_tensorUnitMap_stalk_isIso R P Q x
    exact (bijective_iff_isIso_ofHom _).mpr inferInstance |>.surjective

/-- The comparison morphism from the sheafification of `P ⊗ Q` to the tensor
product of the two sheafifications. -/
noncomputable def comparisonHom
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (CommRingSheaf.directSheafificationFunctor R).obj (P ⊗ Q) ⟶
      CommRingSheaf.tensorObj R
        ((CommRingSheaf.directSheafificationFunctor R).obj P)
        ((CommRingSheaf.directSheafificationFunctor R).obj Q) :=
  (CommRingSheaf.directSheafificationFunctor R).map
    (tensorUnitMap R P Q)

private lemma comparisonHom_isIso
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (comparisonHom R P Q) := by
  have h :
      ((Opens.grothendieckTopology X).W.inverseImage
        (PresheafOfModules.toPresheaf
          (R.obj ⋙ forget₂ CommRingCat RingCat)))
        (tensorUnitMap R P Q) :=
    tensorUnitMap_mem_W R P Q
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (CommRingSheaf.directRingMap R)] at h
  exact h

/-- Sheafification commutes with tensor products, object by object. -/
noncomputable def comparisonIso
    (R : TopCat.Sheaf CommRingCat.{u} X)
    (P Q : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (CommRingSheaf.directSheafificationFunctor R).obj (P ⊗ Q) ≅
      CommRingSheaf.tensorObj R
        ((CommRingSheaf.directSheafificationFunctor R).obj P)
        ((CommRingSheaf.directSheafificationFunctor R).obj Q) := by
  letI := comparisonHom_isIso R P Q
  exact asIso (comparisonHom R P Q)

private lemma unit_naturality
    (R : TopCat.Sheaf CommRingCat.{u} X)
    {P P' : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ P') :
    f ≫ unit R P' =
      unit R P ≫ CommRingSheaf.directHom R
        ((CommRingSheaf.directSheafificationFunctor R).map f) := by
  apply (PresheafOfModules.toPresheaf
    (R.obj ⋙ forget₂ CommRingCat RingCat)).map_injective
  simp only [Functor.map_comp, toPresheaf_map_unit]
  exact CategoryTheory.toSheafify_naturality
    (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map f)

private lemma tensorUnitMap_naturality
    (R : TopCat.Sheaf CommRingCat.{u} X)
    {P P' Q Q' : PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ g) ≫ tensorUnitMap R P' Q' =
      tensorUnitMap R P Q ≫
        (CommRingSheaf.directHom R
            ((CommRingSheaf.directSheafificationFunctor R).map f) ⊗ₘ
          CommRingSheaf.directHom R
            ((CommRingSheaf.directSheafificationFunctor R).map g)) := by
  change (f ⊗ₘ g) ≫ (unit R P' ⊗ₘ unit R Q') =
    (unit R P ⊗ₘ unit R Q) ≫
      (CommRingSheaf.directHom R
          ((CommRingSheaf.directSheafificationFunctor R).map f) ⊗ₘ
        CommRingSheaf.directHom R
          ((CommRingSheaf.directSheafificationFunctor R).map g))
  calc
    _ = (f ≫ unit R P') ⊗ₘ (g ≫ unit R Q') :=
      MonoidalCategory.tensorHom_comp_tensorHom
        f g (unit R P') (unit R Q')
    _ = (unit R P ≫ CommRingSheaf.directHom R
            ((CommRingSheaf.directSheafificationFunctor R).map f)) ⊗ₘ
          (unit R Q ≫ CommRingSheaf.directHom R
            ((CommRingSheaf.directSheafificationFunctor R).map g)) :=
      congrArg₂ (fun a b ↦ a ⊗ₘ b)
        (unit_naturality R f) (unit_naturality R g)
    _ = _ := (MonoidalCategory.tensorHom_comp_tensorHom
      (unit R P) (unit R Q)
      (CommRingSheaf.directHom R
        ((CommRingSheaf.directSheafificationFunctor R).map f))
      (CommRingSheaf.directHom R
        ((CommRingSheaf.directSheafificationFunctor R).map g))).symm

private noncomputable abbrev presheafTensorBifunctor
    (R : TopCat.Sheaf CommRingCat.{u} X) :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u}
      (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- First tensor two module presheaves and then sheafify. -/
noncomputable def sourceFunctor
    (R : TopCat.Sheaf CommRingCat.{u} X) :
    (PresheafOfModules.{u}
        (R.obj ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u}
        (R.obj ⋙ forget₂ CommRingCat RingCat)) ⥤
      CommRingSheaf.Modules
        (J := Opens.grothendieckTopology X) R :=
  presheafTensorBifunctor R ⋙
    CommRingSheaf.directSheafificationFunctor R

/-- Sheafify both module presheaves and then tensor the resulting sheaves. -/
noncomputable def targetFunctor
    (R : TopCat.Sheaf CommRingCat.{u} X) :
    (PresheafOfModules.{u}
        (R.obj ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules.{u}
        (R.obj ⋙ forget₂ CommRingCat RingCat)) ⥤
      CommRingSheaf.Modules
        (J := Opens.grothendieckTopology X) R :=
  Functor.prod
      (CommRingSheaf.directSheafificationFunctor R)
      (CommRingSheaf.directSheafificationFunctor R) ⋙
    CommRingSheaf.tensorBifunctor R

private lemma comparisonHom_naturality
    (R : TopCat.Sheaf CommRingCat.{u} X)
    {PQ P'Q' :
      PresheafOfModules.{u}
          (R.obj ⋙ forget₂ CommRingCat RingCat) ×
        PresheafOfModules.{u}
          (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (f : PQ ⟶ P'Q') :
    (sourceFunctor R).map f ≫
        comparisonHom R P'Q'.1 P'Q'.2 =
      comparisonHom R PQ.1 PQ.2 ≫
        (targetFunctor R).map f := by
  dsimp [sourceFunctor, targetFunctor, presheafTensorBifunctor,
    comparisonHom]
  rw [← MonoidalCategory.tensorHom_def]
  let a := CommRingSheaf.directSheafificationFunctor R
  rw [← a.map_comp]
  change a.map ((f.1 ⊗ₘ f.2) ≫
      tensorUnitMap R P'Q'.1 P'Q'.2) =
    a.map (tensorUnitMap R PQ.1 PQ.2) ≫
      a.map (CommRingSheaf.tensorPresheafHom R
        (a.map f.1) (a.map f.2))
  rw [← a.map_comp]
  apply congrArg a.map
  exact tensorUnitMap_naturality R f.1 f.2

private lemma comparisonIso_naturality
    (R : TopCat.Sheaf CommRingCat.{u} X)
    {PQ P'Q' :
      PresheafOfModules.{u}
          (R.obj ⋙ forget₂ CommRingCat RingCat) ×
        PresheafOfModules.{u}
          (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (f : PQ ⟶ P'Q') :
    (sourceFunctor R).map f ≫
        (comparisonIso R P'Q'.1 P'Q'.2).hom =
      (comparisonIso R PQ.1 PQ.2).hom ≫
        (targetFunctor R).map f := by
  exact comparisonHom_naturality R f

/-- Sheafification commutes naturally with tensor products. -/
noncomputable def comparisonNatIso
    (R : TopCat.Sheaf CommRingCat.{u} X) :
    sourceFunctor R ≅ targetFunctor R :=
  NatIso.ofComponents
    (fun PQ ↦ comparisonIso R PQ.1 PQ.2)
    (comparisonIso_naturality R)

end


end LSZ.SheafificationTensor
