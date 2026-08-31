import LSZ.InverseImageAdjunction
import LSZ.PullbackPresheafTensor

open CategoryTheory TopologicalSpace

namespace LSZ.PullbackPresheaf

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (A : Y.Presheaf CommRingCat.{u})
  (B : X.Presheaf CommRingCat.{u})
  (alpha : LSZ.InverseImagePresheaf.ring f A ⟶ B)

abbrev alphaRing :
    (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) ⟶
      (B ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight alpha (forget₂ CommRingCat RingCat)

abbrev alphaRingId :
    (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) ⟶
      (𝟭 (Opens X)).op ⋙ (B ⋙ forget₂ CommRingCat RingCat) := by
  exact alphaRing f A B alpha

abbrev totalRing :
    (A ⋙ forget₂ CommRingCat RingCat) ⟶
      (Opens.map f).op ⋙ (B ⋙ forget₂ CommRingCat RingCat) :=
  LSZ.InverseImageAdjunction.ringUnit' f A ≫
    Functor.whiskerLeft (Opens.map f).op (alphaRingId f A B alpha)

private noncomputable def rawAdjunction :
    LSZ.PullbackPresheafTensor.functor f A B alpha ⊣
      PresheafOfModules.pushforward.{u}
          (alphaRingId f A B alpha) ⋙
        LSZ.InverseImageAdjunction.pushforward f A := by
  exact (LSZ.InverseImageAdjunction.adjunction f A).comp
    (LSZ.CommRingSheaf.extensionRestrictionPresheafAdjunction alpha)

noncomputable def adjunction :
    LSZ.PullbackPresheafTensor.functor f A B alpha ⊣
      PresheafOfModules.pushforward.{u} (totalRing f A B alpha) :=
  (rawAdjunction f A B alpha).ofNatIsoRight
    (PresheafOfModules.pushforwardComp
      (LSZ.InverseImageAdjunction.ringUnit' f A)
      (alphaRingId f A B alpha))

local instance :
    (PresheafOfModules.pushforward.{u}
      (totalRing f A B alpha)).IsRightAdjoint :=
  (adjunction f A B alpha).isRightAdjoint

noncomputable def pullbackIso :
    LSZ.PullbackPresheafTensor.functor f A B alpha ≅
      PresheafOfModules.pullback.{u} (totalRing f A B alpha) :=
  Adjunction.leftAdjointUniq (adjunction f A B alpha)
    (PresheafOfModules.pullbackPushforwardAdjunction
      (totalRing f A B alpha))

end

end LSZ.PullbackPresheaf
