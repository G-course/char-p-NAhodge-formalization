import LSZ.SheafExtensionTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Geometry.RingedSpace.Basic

/-!
# Modules on ringed spaces

This file contains only the ringed-space interface needed by the tensor/pullback
comparison.  It deliberately does not use any scheme structure.
-/

open CategoryTheory

namespace LSZ.RingedSpace

universe u

noncomputable section

open AlgebraicGeometry TopologicalSpace

variable (X : AlgebraicGeometry.RingedSpace.{u})

/-- The structure sheaf, regarded as a sheaf of (not necessarily commutative)
rings, as required by mathlib's category of module sheaves. -/
abbrev ringSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- Sheaves of modules on a ringed space. -/
abbrev Modules := SheafOfModules.{u} (ringSheaf X)

variable {X : AlgebraicGeometry.RingedSpace.{u}}
  {Y : AlgebraicGeometry.RingedSpace.{u}}

/-- The morphism of sheaves of rings associated with a morphism of ringed
spaces. -/
def toRingSheafHom (f : X ⟶ Y) :
    ringSheaf Y ⟶
      ((Opens.map f.hom.base).sheafPushforwardContinuous
        RingCat.{u} _ _).obj (ringSheaf X) where
  hom := Functor.whiskerRight f.hom.c (forget₂ CommRingCat RingCat.{u})

/-- Pullback of module sheaves along a morphism of ringed spaces. -/
noncomputable def pullback (f : X ⟶ Y) : Modules Y ⥤ Modules X :=
  letI :
      (PresheafOfModules.pushforward.{u} (toRingSheafHom f).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward (toRingSheafHom f).hom
  letI :
      (SheafOfModules.pushforward.{u} (toRingSheafHom f)).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward (toRingSheafHom f)
  SheafOfModules.pullback.{u} (toRingSheafHom f)

end

end LSZ.RingedSpace
