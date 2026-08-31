import LSZ.PullbackPresheaf
import LSZ.RingedSpaceModules
import LSZ.SheafificationTensor

/-!
# Explicit pullback on ringed spaces

The pullback is written as inverse image of module presheaves, extension of
scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, and sheafification.  No scheme structure is used.
-/

open CategoryTheory
open scoped MonoidalCategory

namespace LSZ.RingedSpace

universe u

noncomputable section

open AlgebraicGeometry TopologicalSpace

variable {X Y : AlgebraicGeometry.RingedSpace.{u}}

/-- The adjoint transpose of the structure-presheaf map of a morphism of
ringed spaces. -/
noncomputable def inverseImageStructureMap (f : X ⟶ Y) :
    InverseImagePresheaf.ring f.hom.base Y.sheaf.obj ⟶ X.sheaf.obj :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction
    CommRingCat.{u} f.hom.base).homEquiv Y.sheaf.obj X.sheaf.obj).symm f.hom.c

@[simp]
lemma inverseImageStructureMap_adjunct (f : X ⟶ Y) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv Y.sheaf.obj X.sheaf.obj
        (inverseImageStructureMap f) = f.hom.c :=
  Equiv.apply_symm_apply _ _

/-- Explicit pullback before sheafification. -/
noncomputable def explicitPullbackPresheaf (f : X ⟶ Y) :
    PresheafOfModules.{u}
        (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u}
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  PullbackPresheafTensor.functor f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f)

/-- Explicit pullback of module sheaves: forget to the direct module
presheaf, take inverse image, extend scalars, and sheafify. -/
noncomputable def explicitPullback (f : X ⟶ Y) : Modules Y ⥤ Modules X :=
  CommRingSheaf.directForgetFunctor Y.sheaf ⋙
    explicitPullbackPresheaf f ⋙
      CommRingSheaf.directSheafificationFunctor X.sheaf

/-- The ring map used by the explicit presheaf pullback. -/
abbrev explicitPullbackRingMap (f : X ⟶ Y) :
    (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat) ⟶
      (Opens.map f.hom.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  PullbackPresheaf.totalRing f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f)

/-- The two-step ring map (Kan unit followed by the transposed structure map)
is the original structure-presheaf map. -/
lemma explicitPullbackRingMap_eq (f : X ⟶ Y) :
    explicitPullbackRingMap f = (toRingSheafHom f).hom := by
  let adj := TopCat.Presheaf.pullbackPushforwardAdjunction
    CommRingCat.{u} f.hom.base
  have h := (adj.homEquiv Y.sheaf.obj X.sheaf.obj).apply_symm_apply f.hom.c
  rw [adj.homEquiv_unit] at h
  have h' := congrArg
    (fun q ↦ Functor.whiskerRight q (forget₂ CommRingCat RingCat.{u})) h
  change explicitPullbackRingMap f = (toRingSheafHom f).hom at h'
  exact h'

/-- Before sheafification, the explicit construction is the abstract mathlib
pullback of module presheaves. -/
noncomputable def explicitPullbackPresheafIso (f : X ⟶ Y) :
    explicitPullbackPresheaf f ≅
      PresheafOfModules.pullback.{u} (explicitPullbackRingMap f) :=
  PullbackPresheaf.pullbackIso f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f)

local instance ringedPresheafPushforwardIsRightAdjoint (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u}
      (toRingSheafHom f).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward (toRingSheafHom f).hom

local instance ringedSheafPushforwardIsRightAdjoint (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u}
      (toRingSheafHom f)).IsRightAdjoint :=
  SheafOfModules.instIsRightAdjointPushforward (toRingSheafHom f)

private noncomputable def explicitPushforwardIso (f : X ⟶ Y) :
    PresheafOfModules.pushforward.{u} (explicitPullbackRingMap f) ≅
      PresheafOfModules.pushforward.{u} (toRingSheafHom f).hom :=
  eqToIso (congrArg (fun phi ↦ PresheafOfModules.pushforward.{u} phi)
    (explicitPullbackRingMap_eq f))

private noncomputable def explicitPullbackPresheafAdjunctionToRingHom
    (f : X ⟶ Y) :
    explicitPullbackPresheaf f ⊣
      PresheafOfModules.pushforward.{u} (toRingSheafHom f).hom :=
  (PullbackPresheaf.adjunction f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f)).ofNatIsoRight (explicitPushforwardIso f)

private noncomputable def explicitPullbackHomEquiv (f : X ⟶ Y)
    (M : Modules Y) (N : Modules X) :
    ((explicitPullback f).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.pushforward.{u} (toRingSheafHom f)).obj N) := by
  change ((CommRingSheaf.directSheafificationFunctor X.sheaf).obj
      ((explicitPullbackPresheaf f).obj
        ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)) ⟶ N) ≃ _
  exact ((CommRingSheaf.directSheafificationAdjunction
    X.sheaf).homEquiv _ _).trans <|
      ((explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
        ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
        ((CommRingSheaf.directForgetFunctor X.sheaf).obj N)).trans
      ((CommRingSheaf.directForgetFullyFaithful Y.sheaf).homEquiv
        (X := M)
        (Y := (SheafOfModules.pushforward.{u}
          (toRingSheafHom f)).obj N)).symm

private lemma explicitPullbackHomEquiv_symm_apply (f : X ⟶ Y)
    (M : Modules Y) (N : Modules X)
    (h : M ⟶ (SheafOfModules.pushforward.{u}
      (toRingSheafHom f)).obj N) :
    (explicitPullbackHomEquiv f M N).symm h =
      ((CommRingSheaf.directSheafificationAdjunction
        X.sheaf).homEquiv _ _).symm
        (((explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
          ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
          ((CommRingSheaf.directForgetFunctor X.sheaf).obj N)).symm
            ((CommRingSheaf.directForgetFunctor Y.sheaf).map h)) := by
  rfl

private lemma explicitPullbackHomEquiv_apply (f : X ⟶ Y)
    (M : Modules Y) (N : Modules X)
    (g : (explicitPullback f).obj M ⟶ N) :
    explicitPullbackHomEquiv f M N g =
      ((CommRingSheaf.directForgetFullyFaithful Y.sheaf).homEquiv
        (X := M)
        (Y := (SheafOfModules.pushforward.{u}
          (toRingSheafHom f)).obj N)).symm
        ((explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
          ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
          ((CommRingSheaf.directForgetFunctor X.sheaf).obj N)
          ((CommRingSheaf.directSheafificationAdjunction
            X.sheaf).homEquiv _ _ g)) := by
  rfl

private lemma explicitPullbackHomEquiv_naturality_left_symm (f : X ⟶ Y)
    {M' M : Modules Y} {N : Modules X} (g : M' ⟶ M)
    (h : M ⟶ (SheafOfModules.pushforward.{u}
      (toRingSheafHom f)).obj N) :
    (explicitPullbackHomEquiv f M' N).symm (g ≫ h) =
      (explicitPullback f).map g ≫
        (explicitPullbackHomEquiv f M N).symm h := by
  rw [explicitPullbackHomEquiv_symm_apply,
    explicitPullbackHomEquiv_symm_apply, Functor.map_comp]
  have hp :=
    (explicitPullbackPresheafAdjunctionToRingHom f).homEquiv_naturality_left_symm
      ((CommRingSheaf.directForgetFunctor Y.sheaf).map g)
      ((CommRingSheaf.directForgetFunctor Y.sheaf).map h)
  have hs := (CommRingSheaf.directSheafificationAdjunction
    X.sheaf).homEquiv_naturality_left_symm
      ((explicitPullbackPresheaf f).map
        ((CommRingSheaf.directForgetFunctor Y.sheaf).map g))
      (((explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
        ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
        ((CommRingSheaf.directForgetFunctor X.sheaf).obj N)).symm
          ((CommRingSheaf.directForgetFunctor Y.sheaf).map h))
  have htotal := congrArg
    (fun k ↦ ((CommRingSheaf.directSheafificationAdjunction
      X.sheaf).homEquiv _ N).symm k) hp
  exact htotal.trans hs

private lemma explicitPullbackHomEquiv_naturality_right (f : X ⟶ Y)
    {M : Modules Y} {N N' : Modules X}
    (g : (explicitPullback f).obj M ⟶ N) (h : N ⟶ N') :
    explicitPullbackHomEquiv f M N' (g ≫ h) =
      explicitPullbackHomEquiv f M N g ≫
        (SheafOfModules.pushforward.{u} (toRingSheafHom f)).map h := by
  rw [explicitPullbackHomEquiv_apply, explicitPullbackHomEquiv_apply]
  have hs := (CommRingSheaf.directSheafificationAdjunction
    X.sheaf).homEquiv_naturality_right g h
  have hp :=
    (explicitPullbackPresheafAdjunctionToRingHom f).homEquiv_naturality_right
      ((CommRingSheaf.directSheafificationAdjunction
        X.sheaf).homEquiv _ _ g)
      ((CommRingSheaf.directForgetFunctor X.sheaf).map h)
  have hsp := congrArg
    (fun k ↦ (explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
      ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
      ((CommRingSheaf.directForgetFunctor X.sheaf).obj N') k) hs
  have hmap :
      (PresheafOfModules.pushforward.{u} (toRingSheafHom f).hom).map
          ((CommRingSheaf.directForgetFunctor X.sheaf).map h) =
        (CommRingSheaf.directForgetFunctor Y.sheaf).map
          ((SheafOfModules.pushforward.{u} (toRingSheafHom f)).map h) := by
    rfl
  let a := (explicitPullbackPresheafAdjunctionToRingHom f).homEquiv
    ((CommRingSheaf.directForgetFunctor Y.sheaf).obj M)
    ((CommRingSheaf.directForgetFunctor X.sheaf).obj N)
    ((CommRingSheaf.directSheafificationAdjunction
      X.sheaf).homEquiv _ _ g)
  have hcomp := congrArg (fun q ↦ a ≫ q) hmap
  have hp' := hp.trans hcomp
  have htotal := congrArg
    (fun k ↦ ((CommRingSheaf.directForgetFullyFaithful
      Y.sheaf).homEquiv
        (X := M)
        (Y := (SheafOfModules.pushforward.{u}
          (toRingSheafHom f)).obj N')).symm k)
    (hsp.trans hp')
  let ff := CommRingSheaf.directForgetFullyFaithful Y.sheaf
  let H := (SheafOfModules.pushforward.{u} (toRingSheafHom f)).map h
  have hprecomp := ff.preimage_comp a
    ((CommRingSheaf.directForgetFunctor Y.sheaf).map H)
  have hpremap := ff.preimage_map H
  have hpre := hprecomp.trans
    (congrArg (fun q ↦ ff.preimage a ≫ q) hpremap)
  exact htotal.trans hpre

private noncomputable def explicitPullbackCoreHomEquiv (f : X ⟶ Y) :
    Adjunction.CoreHomEquiv (explicitPullback f)
      (SheafOfModules.pushforward.{u} (toRingSheafHom f)) where
  homEquiv := explicitPullbackHomEquiv f
  homEquiv_naturality_left_symm :=
    explicitPullbackHomEquiv_naturality_left_symm f
  homEquiv_naturality_right :=
    explicitPullbackHomEquiv_naturality_right f

/-- The explicit inverse-image/extension/sheafification construction is left
adjoint to the usual pushforward of module sheaves. -/
noncomputable def explicitPullbackAdjunction (f : X ⟶ Y) :
    explicitPullback f ⊣
      SheafOfModules.pushforward.{u} (toRingSheafHom f) :=
  Adjunction.mkOfHomEquiv (explicitPullbackCoreHomEquiv f)

/-- The explicit inverse-image/extension/sheafification construction is the
abstract mathlib pullback of module sheaves. -/
noncomputable def explicitPullbackIso (f : X ⟶ Y) :
    explicitPullback f ≅ pullback f := by
  change explicitPullback f ≅ SheafOfModules.pullback.{u} (toRingSheafHom f)
  exact Adjunction.leftAdjointUniq (explicitPullbackAdjunction f)
    (SheafOfModules.pullbackPushforwardAdjunction (toRingSheafHom f))

/-- The explicit presheaf pullback is the mathlib presheaf pullback for the
ring map underlying the morphism of ringed spaces.  This formulation avoids
rewriting a ring map underneath a choice of right-adjoint instance. -/
noncomputable def explicitPullbackPresheafIsoToRingHom (f : X ⟶ Y) :
    explicitPullbackPresheaf f ≅
      (@PresheafOfModules.pullback
        _ _ _ _ _ _ _ (toRingSheafHom f).hom
          (ringedPresheafPushforwardIsRightAdjoint f)) :=
  Adjunction.leftAdjointUniq
    (explicitPullbackPresheafAdjunctionToRingHom f)
    (@PresheafOfModules.pullbackPushforwardAdjunction
      _ _ _ _ _ _ _ (toRingSheafHom f).hom
        (ringedPresheafPushforwardIsRightAdjoint f))

/-- Pulling back a sheafification agrees with sheafifying the explicit
presheaf pullback. -/
noncomputable def sheafificationPullbackComparison (f : X ⟶ Y) :
    CommRingSheaf.directSheafificationFunctor Y.sheaf ⋙ pullback f ≅
      explicitPullbackPresheaf f ⋙
        CommRingSheaf.directSheafificationFunctor X.sheaf :=
  SheafOfModules.sheafificationCompPullback (toRingSheafHom f) ≪≫
    (Functor.isoWhiskerRight
      (explicitPullbackPresheafIsoToRingHom f)
      (CommRingSheaf.directSheafificationFunctor X.sheaf)).symm

/-- The tensor comparison for the explicit presheaf pullback, object by
object. -/
noncomputable def explicitPullbackPresheafTensorObjIso
    (f : X ⟶ Y)
    (M N : PresheafOfModules.{u}
      (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    (explicitPullbackPresheaf f).obj (M ⊗ N) ≅
      (explicitPullbackPresheaf f).obj M ⊗
        (explicitPullbackPresheaf f).obj N :=
  PullbackPresheafTensor.tensorObjIso f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f) M N

/-- Explicit pullback before sheafification preserves tensor products,
naturally in both module presheaves. -/
noncomputable def explicitPullbackPresheafTensorNatIso (f : X ⟶ Y) :
    PullbackPresheafTensor.tensorSourceFunctor f.hom.base
        Y.sheaf.obj X.sheaf.obj (inverseImageStructureMap f) ≅
      PullbackPresheafTensor.tensorTargetFunctor f.hom.base
        Y.sheaf.obj X.sheaf.obj (inverseImageStructureMap f) :=
  PullbackPresheafTensor.tensorNatIso f.hom.base Y.sheaf.obj X.sheaf.obj
    (inverseImageStructureMap f)

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

private noncomputable abbrev presheafTensorBifunctor
    (Z : AlgebraicGeometry.RingedSpace.{u}) :=
  Functor.uncurry.obj (MonoidalCategory.curriedTensor
    (PresheafOfModules.{u}
      (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

private noncomputable abbrev directForgetPairFunctor
    (Z : AlgebraicGeometry.RingedSpace.{u}) :=
  Functor.prod
    (CommRingSheaf.directForgetFunctor Z.sheaf)
    (CommRingSheaf.directForgetFunctor Z.sheaf)

private noncomputable abbrev tensorInputPresheafFunctor
    (Z : AlgebraicGeometry.RingedSpace.{u}) :=
  directForgetPairFunctor Z ⋙ presheafTensorBifunctor Z

private noncomputable def sheafTensorPresentationApp
    (Z : AlgebraicGeometry.RingedSpace.{u}) (MN : Modules Z × Modules Z) :
    (CommRingSheaf.tensorBifunctor Z.sheaf).obj MN ≅
      (tensorInputPresheafFunctor Z ⋙
        CommRingSheaf.directSheafificationFunctor Z.sheaf).obj MN :=
  Iso.refl _

private lemma sheafTensorPresentation_map_eq
    (Z : AlgebraicGeometry.RingedSpace.{u})
    {MN PQ : Modules Z × Modules Z} (g : MN ⟶ PQ) :
    (CommRingSheaf.tensorBifunctor Z.sheaf).map g =
      (tensorInputPresheafFunctor Z ⋙
        CommRingSheaf.directSheafificationFunctor Z.sheaf).map g := by
  rw [CommRingSheaf.tensorBifunctor_map Z.sheaf g]
  dsimp [tensorInputPresheafFunctor, directForgetPairFunctor,
    presheafTensorBifunctor, CommRingSheaf.tensorHom]
  rw [← MonoidalCategory.tensorHom_def]
  rfl

private lemma sheafTensorPresentationApp_naturality
    (Z : AlgebraicGeometry.RingedSpace.{u})
    {MN PQ : Modules Z × Modules Z} (g : MN ⟶ PQ) :
    (CommRingSheaf.tensorBifunctor Z.sheaf).map g ≫
        (sheafTensorPresentationApp Z PQ).hom =
      (sheafTensorPresentationApp Z MN).hom ≫
        (tensorInputPresheafFunctor Z ⋙
          CommRingSheaf.directSheafificationFunctor Z.sheaf).map g := by
  have hPQ : (sheafTensorPresentationApp Z PQ).hom = 𝟙 _ := rfl
  have hMN : (sheafTensorPresentationApp Z MN).hom = 𝟙 _ := rfl
  rw [hPQ, hMN]
  exact (Category.comp_id _).trans
    ((sheafTensorPresentation_map_eq Z g).trans
      (Category.id_comp _).symm)

private noncomputable def sheafTensorPresentation
    (Z : AlgebraicGeometry.RingedSpace.{u}) :
    CommRingSheaf.tensorBifunctor Z.sheaf ≅
      tensorInputPresheafFunctor Z ⋙
        CommRingSheaf.directSheafificationFunctor Z.sheaf :=
  NatIso.ofComponents (sheafTensorPresentationApp Z)
    (sheafTensorPresentationApp_naturality Z)

/-- First tensor two module sheaves and then pull back. -/
noncomputable def pullbackTensorSourceFunctor (f : X ⟶ Y) :
    Modules Y × Modules Y ⥤ Modules X :=
  CommRingSheaf.tensorBifunctor Y.sheaf ⋙ pullback f

/-- Pull back two module sheaves and then tensor. -/
noncomputable def pullbackTensorTargetFunctor (f : X ⟶ Y) :
    Modules Y × Modules Y ⥤ Modules X :=
  Functor.prod (pullback f) (pullback f) ⋙
    CommRingSheaf.tensorBifunctor X.sheaf

private noncomputable def explicitPullbackTensorTargetIso
    (f : X ⟶ Y) (M N : Modules Y) :
    CommRingSheaf.tensorObj X.sheaf
        ((explicitPullback f).obj M) ((explicitPullback f).obj N) ≅
      CommRingSheaf.tensorObj X.sheaf
        ((pullback f).obj M) ((pullback f).obj N) := by
  change (CommRingSheaf.tensorBifunctor X.sheaf).obj
      ((explicitPullback f).obj M, (explicitPullback f).obj N) ≅
    (CommRingSheaf.tensorBifunctor X.sheaf).obj
      ((pullback f).obj M, (pullback f).obj N)
  exact (CommRingSheaf.tensorBifunctor X.sheaf).mapIso
    (Iso.prod ((explicitPullbackIso f).app M)
      ((explicitPullbackIso f).app N))

/-- Pullback commutes with tensor products, object by object. -/
noncomputable def pullbackTensorObjIso (f : X ⟶ Y)
    (M N : Modules Y) :
    (pullback f).obj (CommRingSheaf.tensorObj Y.sheaf M N) ≅
      CommRingSheaf.tensorObj X.sheaf
        ((pullback f).obj M) ((pullback f).obj N) := by
  let P := (CommRingSheaf.directForgetFunctor Y.sheaf).obj M
  let Q := (CommRingSheaf.directForgetFunctor Y.sheaf).obj N
  let E := explicitPullbackPresheaf f
  let aX := CommRingSheaf.directSheafificationFunctor X.sheaf
  exact
    (Functor.isoWhiskerRight (sheafTensorPresentation Y)
        (pullback f)).app (M, N) ≪≫
      (Functor.associator (tensorInputPresheafFunctor Y)
        (CommRingSheaf.directSheafificationFunctor Y.sheaf)
          (pullback f)).app (M, N) ≪≫
        (sheafificationPullbackComparison f).app (P ⊗ Q) ≪≫
          aX.mapIso (explicitPullbackPresheafTensorObjIso f P Q) ≪≫
            SheafificationTensor.comparisonIso X.sheaf
              (E.obj P) (E.obj Q) ≪≫
              explicitPullbackTensorTargetIso f M N

private noncomputable def pullbackTensorComparisonStageOne (f : X ⟶ Y) :
    tensorInputPresheafFunctor Y ⋙
        (CommRingSheaf.directSheafificationFunctor Y.sheaf ⋙ pullback f) ≅
      tensorInputPresheafFunctor Y ⋙
        (explicitPullbackPresheaf f ⋙
          CommRingSheaf.directSheafificationFunctor X.sheaf) :=
  Functor.isoWhiskerLeft (tensorInputPresheafFunctor Y)
    (sheafificationPullbackComparison f)

private noncomputable def pullbackTensorComparisonStageTwo (f : X ⟶ Y) :
    directForgetPairFunctor Y ⋙
        (PullbackPresheafTensor.tensorSourceFunctor f.hom.base
          Y.sheaf.obj X.sheaf.obj (inverseImageStructureMap f) ⋙
            CommRingSheaf.directSheafificationFunctor X.sheaf) ≅
      directForgetPairFunctor Y ⋙
        (PullbackPresheafTensor.tensorTargetFunctor f.hom.base
          Y.sheaf.obj X.sheaf.obj (inverseImageStructureMap f) ⋙
            CommRingSheaf.directSheafificationFunctor X.sheaf) :=
  Functor.isoWhiskerLeft (directForgetPairFunctor Y)
    (Functor.isoWhiskerRight
      (explicitPullbackPresheafTensorNatIso f)
      (CommRingSheaf.directSheafificationFunctor X.sheaf))

private noncomputable def pulledPresheafPairFunctor (f : X ⟶ Y) :
    Modules Y × Modules Y ⥤
      PresheafOfModules.{u}
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) ×
        PresheafOfModules.{u}
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  directForgetPairFunctor Y ⋙
    Functor.prod (explicitPullbackPresheaf f)
      (explicitPullbackPresheaf f)

private noncomputable def pullbackTensorComparisonStageThree (f : X ⟶ Y) :
    pulledPresheafPairFunctor f ⋙
        SheafificationTensor.sourceFunctor X.sheaf ≅
      pulledPresheafPairFunctor f ⋙
        SheafificationTensor.targetFunctor X.sheaf :=
  Functor.isoWhiskerLeft (pulledPresheafPairFunctor f)
    (SheafificationTensor.comparisonNatIso X.sheaf)

private noncomputable def pullbackTensorComparisonStageFour (f : X ⟶ Y) :
    Functor.prod (explicitPullback f) (explicitPullback f) ⋙
        CommRingSheaf.tensorBifunctor X.sheaf ≅
      Functor.prod (pullback f) (pullback f) ⋙
        CommRingSheaf.tensorBifunctor X.sheaf :=
  Functor.isoWhiskerRight
    (NatIso.prod (explicitPullbackIso f) (explicitPullbackIso f))
    (CommRingSheaf.tensorBifunctor X.sheaf)

private noncomputable def pullbackTensorComparisonStageZero (f : X ⟶ Y) :
    pullbackTensorSourceFunctor f ≅
      (tensorInputPresheafFunctor Y ⋙
        CommRingSheaf.directSheafificationFunctor Y.sheaf) ⋙ pullback f :=
  Functor.isoWhiskerRight (sheafTensorPresentation Y) (pullback f)

private noncomputable def pullbackTensorComparisonSourceAssociator
    (f : X ⟶ Y) :
    (tensorInputPresheafFunctor Y ⋙
        CommRingSheaf.directSheafificationFunctor Y.sheaf) ⋙ pullback f ≅
      tensorInputPresheafFunctor Y ⋙
        (CommRingSheaf.directSheafificationFunctor Y.sheaf ⋙ pullback f) :=
  Functor.associator _ _ _

private noncomputable def pullbackTensorNatIsoCore (f : X ⟶ Y) :
    pullbackTensorSourceFunctor f ≅ pullbackTensorTargetFunctor f := by
  exact pullbackTensorComparisonStageZero f ≪≫
    pullbackTensorComparisonSourceAssociator f ≪≫
      pullbackTensorComparisonStageOne f ≪≫
        pullbackTensorComparisonStageTwo f ≪≫
          pullbackTensorComparisonStageThree f ≪≫
            pullbackTensorComparisonStageFour f

private lemma pullbackTensorObjIso_eq_core_app (f : X ⟶ Y)
    (M N : Modules Y) :
    pullbackTensorObjIso f M N =
      (pullbackTensorNatIsoCore f).app (M, N) := by
  rfl

private lemma pullbackTensorObjIso_naturality (f : X ⟶ Y)
    {MN PQ : Modules Y × Modules Y} (g : MN ⟶ PQ) :
    (pullbackTensorSourceFunctor f).map g ≫
        (pullbackTensorObjIso f PQ.1 PQ.2).hom =
      (pullbackTensorObjIso f MN.1 MN.2).hom ≫
        (pullbackTensorTargetFunctor f).map g := by
  rw [pullbackTensorObjIso_eq_core_app,
    pullbackTensorObjIso_eq_core_app]
  exact (pullbackTensorNatIsoCore f).hom.naturality g

/-- Pullback of module sheaves commutes naturally with tensor products. -/
noncomputable def pullbackTensorNatIso (f : X ⟶ Y) :
    pullbackTensorSourceFunctor f ≅ pullbackTensorTargetFunctor f :=
  NatIso.ofComponents
    (fun MN ↦ pullbackTensorObjIso f MN.1 MN.2)
    (pullbackTensorObjIso_naturality f)

end

end LSZ.RingedSpace
