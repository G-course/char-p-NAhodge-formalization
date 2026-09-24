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

/-- An additive morphism of presheaves, regarded as a morphism of module
presheaves over the lifted integers. -/
noncomputable def asIntegerModulePresheafMap
    {P Q : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) :
    asIntegerModulePresheaf X P ⟶ asIntegerModulePresheaf X Q := by
  refine PresheafOfModules.homMk
    (M₁ := asIntegerModulePresheaf X P)
    (M₂ := asIntegerModulePresheaf X Q) f ?_
  intro U n m
  change f.app U (n.down • m) = n.down • f.app U m
  exact (f.app U).hom.map_zsmul n.down m

/-- The additive connection tensor formed with an arbitrary coefficient
presheaf. -/
noncomputable abbrev connectionTensorModulePresheafOf
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    PresheafOfModules.{u}
      (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat) :=
  asIntegerModulePresheaf X (vectorFieldAbPresheaf X) ⊗
    asIntegerModulePresheaf X P

/-- The underlying additive presheaf of the connection tensor with
presheaf coefficients. -/
noncomputable abbrev connectionTensorPresheafOf
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (connectionTensorModulePresheafOf X P).presheaf

/-- Functoriality of the connection tensor in its coefficient presheaf. -/
noncomputable def connectionTensorModulePresheafMap
    {P Q : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) :
    connectionTensorModulePresheafOf X P ⟶
      connectionTensorModulePresheafOf X Q :=
  𝟙 (asIntegerModulePresheaf X (vectorFieldAbPresheaf X)) ⊗ₘ
    asIntegerModulePresheafMap X f

/-- Underlying additive-presheaf functoriality of the connection tensor. -/
noncomputable def connectionTensorPresheafMap
    {P Q : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) :
    connectionTensorPresheafOf X P ⟶ connectionTensorPresheafOf X Q :=
  (PresheafOfModules.toPresheaf
    (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat)).map
      (connectionTensorModulePresheafMap X f)

/-- Sheafification of the connection tensor with arbitrary additive
presheaf coefficients. -/
noncomputable def connectionTensorSheafOf
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X.scheme :=
  (presheafToSheaf (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).obj (connectionTensorPresheafOf X P)

/-- Functoriality of the sheafified connection tensor. -/
noncomputable def connectionTensorSheafMap
    {P Q : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) :
    connectionTensorSheafOf X P ⟶ connectionTensorSheafOf X Q :=
  (presheafToSheaf (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).map (connectionTensorPresheafMap X f)

/-- The unit from a presheaf connection tensor to its sheafification. -/
noncomputable def connectionTensorSheafUnit
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    connectionTensorPresheafOf X P ⟶ (connectionTensorSheafOf X P).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).unit.app (connectionTensorPresheafOf X P)

/-- The mathlib module-presheaf tensor underlying contracted connections. -/
noncomputable def connectionTensorModulePresheaf (M : X.scheme.Modules) :
    PresheafOfModules.{u}
      (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat) :=
  connectionTensorModulePresheafOf X M.presheaf

/-- The underlying additive presheaf of the connection tensor. -/
noncomputable def connectionTensorPresheaf (M : X.scheme.Modules) :
    X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  connectionTensorPresheafOf X M.presheaf

/-- Sheafification of `U ↦ ᵊf_X(U) ⊗_ℤ M(U)`. -/
noncomputable def connectionTensor (M : X.scheme.Modules) :
    TopCat.Sheaf AddCommGrpCat.{u} X.scheme :=
  connectionTensorSheafOf X M.presheaf

/-- The canonical map from the module-presheaf tensor into its sheafification. -/
noncomputable def connectionTensorUnit (M : X.scheme.Modules) :
    connectionTensorPresheaf X M ⟶ (connectionTensor X M).obj :=
  connectionTensorSheafUnit X M.presheaf

/-- A pure tensor in the connection tensor with arbitrary presheaf
coefficients. -/
noncomputable def connectionTensorPureOf
    (P : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : X.scheme.Opens) (D : X.VectorField U) (m : P.obj (.op U)) :
    (connectionTensorModulePresheafOf X P).obj (.op U) := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X P
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

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of pure connection tensors in the coefficient
presheaf. -/
@[simp]
lemma connectionTensorPresheafMap_pure
    {P Q : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : P.obj (.op U)) :
    (connectionTensorPresheafMap X f).app (.op U)
        (connectionTensorPureOf X P U D m) =
      connectionTensorPureOf X Q U D (f.app (.op U) m) := by
  rfl

/-- A pure tensor before sheafification. -/
noncomputable def connectionTensorPure (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensorModulePresheaf X M).obj (.op U) :=
  connectionTensorPureOf X M.presheaf U D m

/-- The image of `D ⊗ m` in the connection tensor sheaf. -/
noncomputable def connectionTmul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensor X M).obj.obj (.op U) :=
  (connectionTensorUnit X M).app (.op U) (connectionTensorPure X M U D m)

@[simp]
lemma connectionTensorPure_zero_left (M : X.scheme.Modules)
    (U : X.scheme.Opens) (m : Γ(M, U)) :
    connectionTensorPure X M U 0 m = 0 := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X M.presheaf
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (VF.obj (.op U)) := (VF.obj (.op U)).isModule
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (MF.obj (.op U)) := (MF.obj (.op U)).isModule
  change (0 : VF.obj (.op U)) ⊗ₜ[(liftedIntegerPresheaf X).obj (.op U)]
      (show MF.obj (.op U) from m) = 0
  exact TensorProduct.zero_tmul (R := (liftedIntegerPresheaf X).obj (.op U))
    (VF.obj (.op U)) (show MF.obj (.op U) from m)

lemma connectionTensorPure_add_left (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D E : X.VectorField U) (m : Γ(M, U)) :
    connectionTensorPure X M U (D + E) m =
      connectionTensorPure X M U D m +
        connectionTensorPure X M U E m := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X M.presheaf
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (VF.obj (.op U)) := (VF.obj (.op U)).isModule
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (MF.obj (.op U)) := (MF.obj (.op U)).isModule
  change ((show VF.obj (.op U) from D) + (show VF.obj (.op U) from E)) ⊗ₜ
      (show MF.obj (.op U) from m) = _
  exact TensorProduct.add_tmul (R := (liftedIntegerPresheaf X).obj (.op U))
    (show VF.obj (.op U) from D) (show VF.obj (.op U) from E)
    (show MF.obj (.op U) from m)

@[simp]
lemma connectionTensorPure_zero_right (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) :
    connectionTensorPure X M U D 0 = 0 := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X M.presheaf
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (VF.obj (.op U)) := (VF.obj (.op U)).isModule
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (MF.obj (.op U)) := (MF.obj (.op U)).isModule
  change (show VF.obj (.op U) from D) ⊗ₜ[(liftedIntegerPresheaf X).obj (.op U)]
      (0 : MF.obj (.op U)) = 0
  exact TensorProduct.tmul_zero (R := (liftedIntegerPresheaf X).obj (.op U))
    (MF.obj (.op U)) (show VF.obj (.op U) from D)

lemma connectionTensorPure_add_right (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) (m n : Γ(M, U)) :
    connectionTensorPure X M U D (m + n) =
      connectionTensorPure X M U D m +
        connectionTensorPure X M U D n := by
  let VF := asIntegerModulePresheaf X (vectorFieldAbPresheaf X)
  let MF := asIntegerModulePresheaf X M.presheaf
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (VF.obj (.op U)) := (VF.obj (.op U)).isModule
  letI : Module ((liftedIntegerPresheaf X).obj (.op U))
      (MF.obj (.op U)) := (MF.obj (.op U)).isModule
  change (show VF.obj (.op U) from D) ⊗ₜ
      ((show MF.obj (.op U) from m) + (show MF.obj (.op U) from n)) = _
  exact TensorProduct.tmul_add (R := (liftedIntegerPresheaf X).obj (.op U))
    (show VF.obj (.op U) from D) (show MF.obj (.op U) from m)
    (show MF.obj (.op U) from n)

@[simp]
lemma connectionTmul_zero_left (M : X.scheme.Modules)
    (U : X.scheme.Opens) (m : Γ(M, U)) :
    connectionTmul X M U 0 m = 0 := by
  unfold connectionTmul
  rw [connectionTensorPure_zero_left]
  exact map_zero ((connectionTensorUnit X M).app (.op U)).hom

lemma connectionTmul_add_left (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D E : X.VectorField U) (m : Γ(M, U)) :
    connectionTmul X M U (D + E) m =
      connectionTmul X M U D m + connectionTmul X M U E m := by
  unfold connectionTmul
  rw [connectionTensorPure_add_left]
  exact map_add ((connectionTensorUnit X M).app (.op U)).hom _ _

@[simp]
lemma connectionTmul_zero_right (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) :
    connectionTmul X M U D 0 = 0 := by
  unfold connectionTmul
  rw [connectionTensorPure_zero_right]
  exact map_zero ((connectionTensorUnit X M).app (.op U)).hom

lemma connectionTmul_add_right (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U) (m n : Γ(M, U)) :
    connectionTmul X M U D (m + n) =
      connectionTmul X M U D m + connectionTmul X M U D n := by
  unfold connectionTmul
  rw [connectionTensorPure_add_right]
  exact map_add ((connectionTensorUnit X M).app (.op U)).hom _ _

lemma connectionTensorPure_restrict (M : X.scheme.Modules)
    {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensorModulePresheaf X M).map (homOfLE hVU).op
        (connectionTensorPure X M U D m) =
      connectionTensorPure X M V (D.restrict hVU)
        (M.val.map (homOfLE hVU).op m) := by
  exact PresheafOfModules.Monoidal.tensorObj_map_tmul
    (M₁ := asIntegerModulePresheaf X (vectorFieldAbPresheaf X))
    (M₂ := asIntegerModulePresheaf X M.presheaf)
    (homOfLE hVU).op D m

@[simp]
lemma connectionTmul_restrict (M : X.scheme.Modules)
    {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensor X M).obj.map (homOfLE hVU).op
        (connectionTmul X M U D m) =
      connectionTmul X M V (D.restrict hVU)
        (M.val.map (homOfLE hVU).op m) := by
  have hn := CategoryTheory.congr_fun
    ((connectionTensorUnit X M).naturality (homOfLE hVU).op)
    (connectionTensorPure X M U D m)
  change (connectionTensorUnit X M).app (.op V)
      ((connectionTensorModulePresheaf X M).map (homOfLE hVU).op
        (connectionTensorPure X M U D m)) =
    (connectionTensor X M).obj.map (homOfLE hVU).op
      ((connectionTensorUnit X M).app (.op U)
        (connectionTensorPure X M U D m)) at hn
  exact hn.symm.trans (congrArg ((connectionTensorUnit X M).app (.op V))
    (connectionTensorPure_restrict X M hVU D m))

lemma connectionTensorModulePresheafMap_id
    (P : Functor X.scheme.Opensᵒᵖ AddCommGrpCat.{u}) :
    connectionTensorModulePresheafMap X (𝟙 P) =
      𝟙 (connectionTensorModulePresheafOf X P) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro D m
  rfl

lemma connectionTensorModulePresheafMap_comp
    {P Q S : Functor X.scheme.Opensᵒᵖ AddCommGrpCat.{u}}
    (f : P ⟶ Q) (g : Q ⟶ S) :
    connectionTensorModulePresheafMap X (f ≫ g) =
      connectionTensorModulePresheafMap X f ≫
        connectionTensorModulePresheafMap X g := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro D m
  rfl

lemma connectionTensorPresheafMap_id
    (P : Functor X.scheme.Opensᵒᵖ AddCommGrpCat.{u}) :
    connectionTensorPresheafMap X (𝟙 P) =
      𝟙 (connectionTensorPresheafOf X P) := by
  let F := PresheafOfModules.toPresheaf
    (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat)
  exact (congrArg F.map
    (connectionTensorModulePresheafMap_id X P)).trans
      (F.map_id (connectionTensorModulePresheafOf X P))

lemma connectionTensorPresheafMap_comp
    {P Q S : Functor X.scheme.Opensᵒᵖ AddCommGrpCat.{u}}
    (f : P ⟶ Q) (g : Q ⟶ S) :
    connectionTensorPresheafMap X (f ≫ g) =
      connectionTensorPresheafMap X f ≫ connectionTensorPresheafMap X g := by
  let F := PresheafOfModules.toPresheaf
    (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat)
  exact (congrArg F.map
    (connectionTensorModulePresheafMap_comp X f g)).trans
      (F.map_comp (connectionTensorModulePresheafMap X f)
        (connectionTensorModulePresheafMap X g))

/-- Functoriality of the additive connection tensor in a module-sheaf
morphism. -/
noncomputable def connectionTensorMap {M N : X.scheme.Modules} (f : M ⟶ N) :
    connectionTensor X M ⟶ connectionTensor X N :=
  connectionTensorSheafMap X
    ((PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map f.val)

@[simp]
lemma connectionTensorMap_tmul {M N : X.scheme.Modules} (f : M ⟶ N)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M, U)) :
    (connectionTensorMap X f).hom.app (.op U) (connectionTmul X M U D m) =
      connectionTmul X N U D (f.app U m) := by
  let g : M.presheaf ⟶ N.presheaf :=
    (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map f.val
  have hn := (sheafificationAdjunction
    (Opens.grothendieckTopology X.scheme) AddCommGrpCat.{u}).unit.naturality
      (connectionTensorPresheafMap X g)
  have hnU := congrArg (fun q ↦ q.app (.op U)) hn
  have hnt := congrArg
    (fun q ↦ q.hom (connectionTensorPure X M U D m)) hnU
  change (connectionTensorMap X f).hom.app (.op U)
      ((connectionTensorUnit X M).app (.op U)
        (connectionTensorPure X M U D m)) =
    (connectionTensorUnit X N).app (.op U)
      (connectionTensorPure X N U D (f.app U m))
  change (connectionTensorUnit X N).app (.op U)
      ((connectionTensorPresheafMap X g).app (.op U)
        (connectionTensorPure X M U D m)) =
    (connectionTensorMap X f).hom.app (.op U)
      ((connectionTensorUnit X M).app (.op U)
        (connectionTensorPure X M U D m)) at hnt
  exact hnt.symm.trans (congrArg ((connectionTensorUnit X N).app (.op U))
    (connectionTensorPresheafMap_pure X g U D m))

@[simp]
lemma connectionTensorMap_id (M : X.scheme.Modules) :
    connectionTensorMap X (𝟙 M) = 𝟙 (connectionTensor X M) := by
  let idM : M ⟶ M := 𝟙 M
  have hforget :
      (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
          idM.val = 𝟙 M.presheaf := by
    change (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
        (𝟙 M.val) = 𝟙 M.presheaf
    exact (PresheafOfModules.toPresheaf
      X.scheme.ringCatSheaf.obj).map_id M.val
  change connectionTensorMap X idM = 𝟙 (connectionTensor X M)
  let F := presheafToSheaf
    (Opens.grothendieckTopology X.scheme) AddCommGrpCat.{u}
  have hp : connectionTensorPresheafMap X
      ((PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
        idM.val) = 𝟙 (connectionTensorPresheafOf X M.presheaf) :=
    (congrArg (connectionTensorPresheafMap X) hforget).trans
      (connectionTensorPresheafMap_id X M.presheaf)
  exact (congrArg F.map hp).trans
    (F.map_id (connectionTensorPresheafOf X M.presheaf))

@[simp]
lemma connectionTensorMap_comp {M N P : X.scheme.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    connectionTensorMap X (f ≫ g) =
      connectionTensorMap X f ≫ connectionTensorMap X g := by
  have hforget :
      (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
          (f ≫ g).val =
        (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map f.val ≫
          (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map g.val := by
    change (PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
        (f.val ≫ g.val) = _
    exact (PresheafOfModules.toPresheaf
      X.scheme.ringCatSheaf.obj).map_comp f.val g.val
  unfold connectionTensorMap connectionTensorSheafMap
  let F := presheafToSheaf
    (Opens.grothendieckTopology X.scheme) AddCommGrpCat.{u}
  let f' := (PresheafOfModules.toPresheaf
    X.scheme.ringCatSheaf.obj).map f.val
  let g' := (PresheafOfModules.toPresheaf
    X.scheme.ringCatSheaf.obj).map g.val
  have hp : connectionTensorPresheafMap X
      ((PresheafOfModules.toPresheaf X.scheme.ringCatSheaf.obj).map
        (f ≫ g).val) =
      connectionTensorPresheafMap X f' ≫
        connectionTensorPresheafMap X g' :=
    (congrArg (connectionTensorPresheafMap X) hforget).trans
      (connectionTensorPresheafMap_comp X f' g')
  exact (congrArg F.map hp).trans
    (F.map_comp (connectionTensorPresheafMap X f')
      (connectionTensorPresheafMap X g'))

end

end LSZ.SmoothScheme
