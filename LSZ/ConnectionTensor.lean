import LSZ.TangentSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The additive tensor sheaf used by a connection

A connection is additive, but not `ᵊa_X`-linear, in its coefficient
section. Its contracted form therefore starts from mathlib's tensor of
module presheaves representing `ᵊf_X(U) ⊗_ℤ M(U)`, and is then sheafified.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- The constant integer ring in the ambient universe. Its action is
definitionally the usual integer action via `ULift.down`. -/
abbrev liftedIntegerPresheaf : X.scheme.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const X.scheme.Opensᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))

/-- An additive presheaf, regarded canonically as a presheaf of modules over
the universe-lifted integers. -/
noncomputable def asIntegerModulePresheaf
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) : PresheafOfModules.{u}
      (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat) := by
  letI (U : X.scheme.Opensᵒᵖ) :
      Module ((liftedIntegerPresheaf X ⋙
        forget₂ CommRingCat RingCat).obj U) (P.obj U) := by
    change Module (ULift.{u} ℤ) (P.obj U)
    infer_instance
  apply PresheafOfModules.ofPresheaf P
  intro U V f n m
  change P.map f (n.down • m) = n.down • P.map f m
  exact (P.map f).hom.map_zsmul n.down m

/-- The mathlib module-presheaf tensor underlying contracted connections. -/
noncomputable def connectionTensorModulePresheaf (M : X.scheme.Modules) :
    PresheafOfModules.{u}
      (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat) :=
  asIntegerModulePresheaf X (vectorFieldAbPresheaf X) ⊗
    asIntegerModulePresheaf X M.presheaf

/-- The underlying additive presheaf of the connection tensor. -/
noncomputable def connectionTensorPresheaf (M : X.scheme.Modules) :
    X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (connectionTensorModulePresheaf X M).presheaf

/-- Sheafification of `U ↦ ᵊf_X(U) ⊗_ℤ M(U)`. -/
noncomputable def connectionTensor (M : X.scheme.Modules) :
    TopCat.Sheaf AddCommGrpCat.{u} X.scheme :=
  (presheafToSheaf (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).obj (connectionTensorPresheaf X M)

/-- The canonical map from the module-presheaf tensor into its sheafification. -/
noncomputable def connectionTensorUnit (M : X.scheme.Modules) :
    connectionTensorPresheaf X M ⟶ (connectionTensor X M).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).unit.app (connectionTensorPresheaf X M)

/-- A pure tensor before sheafification. -/
noncomputable def connectionTensorPure (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensorModulePresheaf X M).obj (.op U) := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X M.presheaf
  letI : Module
      ((liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      (VF.obj (.op U)) := (VF.obj (.op U)).isModule
  letI : Module
      ((liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      (MF.obj (.op U)) := (MF.obj (.op U)).isModule
  change TensorProduct ((liftedIntegerPresheaf X).obj (.op U))
    (VF.obj (.op U)) (MF.obj (.op U))
  let D' : VF.obj (.op U) := by
    dsimp [VF, asIntegerModulePresheaf]
    exact D
  let m' : MF.obj (.op U) := by
    dsimp [MF, asIntegerModulePresheaf]
    exact m
  exact D' ⊗ₜ[(liftedIntegerPresheaf X).obj (.op U)] m'

/-- The image of `D ⊗ m` in the connection tensor sheaf. -/
noncomputable def connectionTmul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensor X M).obj.obj (.op U) :=
  (connectionTensorUnit X M).app (.op U) (connectionTensorPure X M U D m)

end

end LSZ.SmoothScheme
