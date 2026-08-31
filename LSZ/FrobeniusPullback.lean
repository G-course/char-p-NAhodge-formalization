import LSZ.AbsoluteFrobenius
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Frobenius pullback on affine charts

The underlying pullback in this file is always mathlib's
`Scheme.Modules.pullback`.  The main categorical lemma identifies pullback
of `M˜` along `Spec.map φ` with the tilde sheaf associated to extension of
scalars along `φ`.  Its quasicoherent corollary gives the expected affine
formula `S ⊗_R Γ(F)`.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace LSZ

universe u

noncomputable section

namespace AffinePullback

variable {R S : CommRingCat.{u}} (phi : R ⟶ S)

/-- The right adjoints in the affine pullback formula agree: pushforward
followed by global sections is restriction of scalars on global sections. -/
noncomputable def pushforwardGammaIso :
    AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Spec.map phi) ⋙
        AlgebraicGeometry.moduleSpecΓFunctor (R := R) ≅
      AlgebraicGeometry.moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars phi.hom :=
  NatIso.ofComponents (fun M ↦ by
    let evR := TopCat.Sheaf.forget (ModuleCat R)
        (AlgebraicGeometry.Spec R) ⋙
      (evaluation (AlgebraicGeometry.Spec R).Opensᵒᵖ
        (ModuleCat R)).obj (.op ⊤)
    exact evR.mapIso
      ((AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso phi).app M))

/-- Composite adjunction whose left adjoint is tilde followed by pullback. -/
noncomputable def pullbackTildeAdjunction :
    AlgebraicGeometry.tilde.functor R ⋙
        AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Spec.map phi) ⊣
      AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Spec.map phi) ⋙
        AlgebraicGeometry.moduleSpecΓFunctor (R := R) :=
  (AlgebraicGeometry.tilde.adjunction (R := R)).comp
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Spec.map phi))

/-- Composite adjunction whose left adjoint is extension of scalars followed
by tilde. -/
noncomputable def extendTildeAdjunction :
    ModuleCat.extendScalars phi.hom ⋙
        AlgebraicGeometry.tilde.functor S ⊣
      AlgebraicGeometry.moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars phi.hom :=
  (ModuleCat.extendRestrictScalarsAdj phi.hom).comp
    (AlgebraicGeometry.tilde.adjunction (R := S))

/-- Pullback of an affine tilde sheaf is tilde of extension of scalars:
`(Spec.map φ)⁺(M˜) ≅ (S ⊗_R M)˜`. -/
noncomputable def pullbackTildeIso :
    AlgebraicGeometry.tilde.functor R ⋙
        AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Spec.map phi) ≅
      ModuleCat.extendScalars phi.hom ⋙
        AlgebraicGeometry.tilde.functor S :=
  (pullbackTildeAdjunction phi).leftAdjointUniq
    ((extendTildeAdjunction phi).ofNatIsoRight
      (pushforwardGammaIso phi).symm)

/-- Pullback of a quasicoherent module on an affine scheme is the tilde
sheaf of its scalar extension. -/
noncomputable def pullbackQuasicoherentIso
    (F : (AlgebraicGeometry.Spec R).Modules) [F.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Spec.map phi)).obj F ≅
      (AlgebraicGeometry.tilde.functor S).obj
        ((ModuleCat.extendScalars phi.hom).obj
          ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F)) := by
  letI : IsIso F.fromTildeΓ :=
    AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  exact (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Spec.map phi)).mapIso
        (asIso F.fromTildeΓ)).symm).trans
    ((pullbackTildeIso phi).app
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F))

/-- Global sections of affine pullback are extension of scalars:
`Γ((Spec.map φ)⁺F) ≅ S ⊗_R Γ(F)` for quasicoherent `F`. -/
noncomputable def pullbackQuasicoherentTopIso
    (F : (AlgebraicGeometry.Spec R).Modules) [F.IsQuasicoherent] :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := S)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Spec.map phi)).obj F) ≅
      (ModuleCat.extendScalars phi.hom).obj
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F) :=
  ((AlgebraicGeometry.moduleSpecΓFunctor (R := S)).mapIso
    (pullbackQuasicoherentIso phi F)).trans
      (AlgebraicGeometry.tilde.toTildeΓNatIso.app
        ((ModuleCat.extendScalars phi.hom).obj
          ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F))).symm

variable {Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Inverse image commutes with restriction to an open subset.  The source
is restricted to `f⁻¹(U)`, while the target is first restricted to `U` and
then pulled back along the restricted morphism `f |_ U`. -/
noncomputable def restrictPullbackIso (f : Y ⟶ Z) (U : Z.Opens) :
    AlgebraicGeometry.Scheme.Modules.pullback f ⋙
        AlgebraicGeometry.Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι ⋙
        AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U) :=
  (Functor.isoWhiskerLeft
      (AlgebraicGeometry.Scheme.Modules.pullback f)
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
        (f ⁻¹ᵁ U).ι)).trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (AlgebraicGeometry.morphismRestrict_ι f U)).symm.trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (f ∣_ U) U.ι).symm.trans
    (Functor.isoWhiskerRight
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U))).symm)))

end AffinePullback

namespace FrobeniusPullback

variable {p : ℕ} [Fact p.Prime]
variable (X : AlgebraicGeometry.Scheme.{u}) [IsCharacteristicP X p]

/-- Frobenius pullback of an `𝒪_X`-module, using mathlib's module
pullback functor. -/
noncomputable abbrev carrier
    (F : X.Modules) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback
    (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X)).obj F

/-- The Frobenius twist of a module over the coordinate ring of an open
subset.  It is mathlib's extension of scalars along the `p`-power map, hence
its underlying affine expression is `A ⊗_{A,F_A} M`. -/
noncomputable abbrev twist (U : X.Opens)
    (M : ModuleCat Γ(X, U)) : ModuleCat Γ(X, U) :=
  (ModuleCat.extendScalars
    ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X).app U).hom).obj M

/-- On an affine chart, pullback along the chart Frobenius has global
sections equal to the Frobenius twist. -/
noncomputable def affineChartTopIso (U : X.Opens)
    (F : (AlgebraicGeometry.Spec Γ(X, U)).Modules)
    [F.IsQuasicoherent] :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Spec.map
            ((AlgebraicGeometry.Scheme.absoluteFrobenius
              (p := p) X).app U))).obj F) ≅
      twist (p := p) X U
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X, U))).obj F) :=
  AffinePullback.pullbackQuasicoherentTopIso
    ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X).app U) F

/-- The restriction of a module to an affine open, transported through the
canonical affine chart `U ≅ Spec Γ(U, 𝒪_X)`. -/
noncomputable abbrev chartModule (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (F : X.Modules) :
    (AlgebraicGeometry.Spec Γ(X, U)).Modules :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj F)

/-- Frobenius pullback restricted to the inverse image of `U`, then
transported through the affine chart of that inverse image.  Absolute
Frobenius has `F_X⁻¹(U) = U` by `absoluteFrobenius_preimage`; retaining the
inverse-image expression keeps all dependent scheme types canonical. -/
noncomputable abbrev restrictedCarrierChart (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (F : X.Modules) :
    (AlgebraicGeometry.Spec Γ(X, U)).Modules :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor
    (hU.preimage
      (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X)).isoSpec.inv).obj
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
      ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X) ⁻¹ᵁ U).ι).obj
      (carrier (p := p) X F))

/-- After affine-chart transport, pullback by the restricted absolute
Frobenius is pullback by `Spec.map(F_A)`, where `F_A(a) = a^p`. -/
noncomputable def localPullbackChartIso (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X ∣_ U) ⋙
        AlgebraicGeometry.Scheme.Modules.restrictFunctor
          (hU.preimage
            (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X)).isoSpec.inv ≅
      AlgebraicGeometry.Scheme.Modules.restrictFunctor hU.isoSpec.inv ⋙
        AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Spec.map
            ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X).app U)) := by
  let f := AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X
  let hpre := hU.preimage f
  have hSquare :
      hpre.isoSpec.hom ≫ AlgebraicGeometry.Spec.map (f.app U) =
        (f ∣_ U) ≫ hU.isoSpec.hom :=
    AlgebraicGeometry.Scheme.absoluteFrobenius_on_affine (p := p) X U hU
  have hEq :
      hpre.isoSpec.inv ≫ (f ∣_ U) =
        AlgebraicGeometry.Spec.map (f.app U) ≫ hU.isoSpec.inv := by
    rw [← cancel_epi hpre.isoSpec.hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hSquare]
    simp
  exact
    (Functor.isoWhiskerLeft
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U))
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
        hpre.isoSpec.inv)).trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp hpre.isoSpec.inv
      (f ∣_ U)).trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hEq).trans
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Spec.map (f.app U)) hU.isoSpec.inv).symm.trans
    (Functor.isoWhiskerRight
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
        hU.isoSpec.inv)
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Spec.map (f.app U)))).symm)))

/-- Sheaf-level local affine formula for Frobenius pullback. -/
noncomputable def chartedRestrictionIso (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (F : X.Modules) :
    restrictedCarrierChart (p := p) X U hU F ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Spec.map
          ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X).app U))).obj
        (chartModule X U hU F) :=
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
    (hU.preimage
      (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X)).isoSpec.inv).mapIso
    ((AffinePullback.restrictPullbackIso
      (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X) U).app F)).trans
    ((localPullbackChartIso X U hU).app
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj F))

/-- **Affine-local Frobenius-twist formula.**  For a quasicoherent module
`F`, the Frobenius pullback restricted to an affine open and transported to
`Spec A` has module of sections

`A ⊗_{A, F_A} Γ(U, F)`, where `A = Γ(U, 𝒪_X)` and `F_A(a) = a^p`.

The two occurrences of global sections below are mathlib's affine
`moduleSpecΓFunctor`; `twist` is `ModuleCat.extendScalars` along the map whose
pointwise formula was proved in `absoluteFrobenius_app_apply`. -/
noncomputable def restrictedTopIso (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (F : X.Modules)
    [F.IsQuasicoherent] :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X, U))).obj
      (restrictedCarrierChart (p := p) X U hU F) ≅
      twist (p := p) X U
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X, U))).obj
          (chartModule X U hU F)) :=
  ((AlgebraicGeometry.moduleSpecΓFunctor (R := Γ(X, U))).mapIso
    (chartedRestrictionIso X U hU F)).trans
      (AffinePullback.pullbackQuasicoherentTopIso
        ((AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X).app U)
        (chartModule X U hU F))

end FrobeniusPullback

end


end LSZ
