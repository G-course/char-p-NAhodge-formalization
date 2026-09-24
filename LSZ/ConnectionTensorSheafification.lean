import LSZ.ConnectionTensor
import LSZ.StalkTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification of the connection tensor

For an additive coefficient presheaf `P`, tensoring the sheafification unit
`P -> aP` with the vector-field presheaf is a stalkwise isomorphism after
sheafification.  Consequently

`a(T_X tensor_Z P) ~= a(T_X tensor_Z aP)`.

This is the comparison needed to descend a restriction-compatible
presheaf connection to the sheafification of its coefficient presheaf.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

private lemma locallyInjective_of_stalk_injective
    {F G : X.scheme.Opensᵒᵖ ⥤ Ab.{u}} (f : F ⟶ G)
    (hf : ∀ x : X.scheme,
      Function.Injective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.scheme) f := by
  constructor
  intro U s t hst
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have hgerm :
      TopCat.Presheaf.germ F U.unop x hx s =
        TopCat.Presheaf.germ F U.unop x hx t := by
    apply hf x
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply, hst]
  obtain ⟨V, hxV, i₁, i₂, hV⟩ :=
    TopCat.Presheaf.germ_eq F x hx hx s t hgerm
  refine ⟨V, i₁, ?_, hxV⟩
  change F.map i₁.op s = F.map i₁.op t
  simpa only [Subsingleton.elim i₂ i₁] using hV

private lemma coefficientStalkMap_isIso
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (x : X.scheme) :
    IsIso (StalkTensor.map (liftedIntegerPresheaf X) x
      (asIntegerModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P))) := by
  rw [← isIso_iff_of_reflects_iso
    (StalkTensor.map (liftedIntegerPresheaf X) x
      (asIntegerModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P)))
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk
      (C := CommRingCat.{u}) (liftedIntegerPresheaf X) x)) Ab)]
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X.scheme) P))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x Ab.{u} P

private lemma vectorFieldStalkMap_id_isIso (x : X.scheme) :
    IsIso (StalkTensor.map (liftedIntegerPresheaf X) x
      (𝟙 (asIntegerModulePresheaf X (vectorFieldAbPresheaf X)))) := by
  rw [← isIso_iff_of_reflects_iso
    (StalkTensor.map (liftedIntegerPresheaf X) x
      (𝟙 (asIntegerModulePresheaf X (vectorFieldAbPresheaf X))))
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk
      (C := CommRingCat.{u}) (liftedIntegerPresheaf X) x)) Ab)]
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (𝟙 _))
  infer_instance

private lemma tensorStalkMap_isIso
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (x : X.scheme) :
    IsIso (StalkTensor.map (liftedIntegerPresheaf X) x
      (connectionTensorModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P))) := by
  change IsIso (StalkTensor.map (liftedIntegerPresheaf X) x
    ((𝟙 (asIntegerModulePresheaf X (vectorFieldAbPresheaf X))) ⊗ₘ
      asIntegerModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P)))
  letI := vectorFieldStalkMap_id_isIso X x
  letI := coefficientStalkMap_isIso X P x
  exact IsIso.of_isIso_fac_right
    (StalkTensor.tensorIso_naturality (liftedIntegerPresheaf X) x
      (𝟙 (asIntegerModulePresheaf X (vectorFieldAbPresheaf X)))
      (asIntegerModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P)))

private lemma underlyingTensorStalkMap_isIso
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (x : X.scheme) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (connectionTensorPresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P))) := by
  letI := tensorStalkMap_isIso X P x
  change IsIso ((forget₂ (ModuleCat (TopCat.Presheaf.stalk
      (C := CommRingCat.{u}) (liftedIntegerPresheaf X) x)) Ab).map
    (StalkTensor.map (liftedIntegerPresheaf X) x
      (connectionTensorModulePresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P))))
  infer_instance

private lemma tensorSheafificationUnit_mem_W
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (Opens.grothendieckTopology X.scheme).W
      (connectionTensorPresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P)) := by
  rw [(Opens.grothendieckTopology X.scheme).W_iff_isLocallyBijective]
  constructor
  · apply locallyInjective_of_stalk_injective X
    intro x
    letI := underlyingTensorStalkMap_isIso X P x
    exact (bijective_iff_isIso_ofHom _).mpr inferInstance |>.injective
  · apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2
    intro x
    letI := underlyingTensorStalkMap_isIso X P x
    exact (bijective_iff_isIso_ofHom _).mpr inferInstance |>.surjective

private lemma connectionTensorSheafificationMap_isIso
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIso (connectionTensorSheafMap X
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P)) := by
  have h := tensorSheafificationUnit_mem_W X P
  rw [(Opens.grothendieckTopology X.scheme).W_iff] at h
  exact h

/-- Sheafifying before or after inserting the coefficient sheafification
unit in the connection tensor gives naturally isomorphic sheaves. -/
noncomputable def connectionTensorSheafificationIso
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    connectionTensorSheafOf X P ≅
      connectionTensorSheafOf X
        ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
          AddCommGrpCat.{u}).obj P).obj := by
  letI := connectionTensorSheafificationMap_isIso X P
  exact asIso (connectionTensorSheafMap X
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X.scheme) P))

/-- Formula for the comparison on elements coming from the presheaf
connection tensor. -/
lemma connectionTensorSheafificationIso_hom_unit
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : X.scheme.Opensᵒᵖ) (t : (connectionTensorPresheafOf X P).obj U) :
    (connectionTensorSheafificationIso X P).hom.hom.app U
        ((connectionTensorSheafUnit X P).app U t) =
      (connectionTensorSheafUnit X
          ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
            AddCommGrpCat.{u}).obj P).obj).app U
        ((connectionTensorPresheafMap X
          (CategoryTheory.toSheafify
            (Opens.grothendieckTopology X.scheme) P)).app U t) := by
  let f := connectionTensorPresheafMap X
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X.scheme) P)
  have hn := (sheafificationAdjunction
    (Opens.grothendieckTopology X.scheme) AddCommGrpCat.{u}).unit.naturality f
  have hnU := congrArg (fun q ↦ q.app U) hn
  have hnt := congrArg (fun q ↦ q.hom t) hnU
  exact hnt.symm

end

end LSZ.SmoothScheme
