import LSZ.SheafTensor
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Internal Hom for sheaves of modules on a ringed space

For sheaves of modules over a sheaf of commutative rings on a topological space, this file
constructs the internal Hom sheaf and proves the tensor--Hom adjunction

`Hom(M ⊗ N, P) ≃ Hom(M, 𝓗om(N, P))`.

The construction is made on ringed spaces; no scheme, quasi-coherence, smoothness, or
characteristic hypothesis is used.
-/

open CategoryTheory TopologicalSpace Opposite

namespace LSZ.CommRingSheaf

universe u

noncomputable section

abbrev topRingSheaf {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :=
  ringSheaf.{u, u, u} R

abbrev RingedModules {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :=
  Modules.{u, u, u} R

variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
variable (M N : RingedModules R)

def homRestrictFun {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (φ : M.over U.unop ⟶ N.over U.unop) :
    M.over V.unop ⟶ N.over V.unop :=
  ((SheafOfModules.overFunctorMap (topRingSheaf R) f.unop).app M).inv ≫
    (SheafOfModules.overMap (topRingSheaf R) f.unop).map φ ≫
      ((SheafOfModules.overFunctorMap (topRingSheaf R) f.unop).app N).hom

private lemma homRestrictFun_zero {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    homRestrictFun R M N f 0 = 0 := by
  apply SheafOfModules.hom_ext
  ext W w
  rfl

private lemma homRestrictFun_add {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (φ ψ : M.over U.unop ⟶ N.over U.unop) :
    homRestrictFun R M N f (φ + ψ) =
      homRestrictFun R M N f φ + homRestrictFun R M N f ψ := by
  apply SheafOfModules.hom_ext
  ext W w
  rfl

def homRestrict {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (M.over U.unop ⟶ N.over U.unop) →+
      (M.over V.unop ⟶ N.over V.unop) where
  toFun := homRestrictFun R M N f
  map_zero' := homRestrictFun_zero R M N f
  map_add' := homRestrictFun_add R M N f

private def homAbPresheafObj (U : (Opens X)ᵒᵖ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (M.over U.unop ⟶ N.over U.unop)

private def homAbPresheafMap {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    homAbPresheafObj R M N U ⟶ homAbPresheafObj R M N V :=
  AddCommGrpCat.ofHom (homRestrict R M N f)

private lemma homAbPresheaf_map_id (U : (Opens X)ᵒᵖ) :
    AddCommGrpCat.ofHom (homRestrict R M N (𝟙 U)) = 𝟙 _ := by
  ext φ
  rfl

private lemma homAbPresheaf_map_comp {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    AddCommGrpCat.ofHom (homRestrict R M N (f ≫ g)) =
      AddCommGrpCat.ofHom (homRestrict R M N f) ≫
        AddCommGrpCat.ofHom (homRestrict R M N g) := by
  ext φ
  rfl

def homAbPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj := homAbPresheafObj R M N
  map := homAbPresheafMap R M N
  map_id := homAbPresheaf_map_id R M N
  map_comp := homAbPresheaf_map_comp R M N

def overScalar (U : Opens X) (V : (Over U)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj (op U)) :
    ((topRingSheaf R).over U).obj.obj V := by
  change (topRingSheaf R).obj.obj (op V.unop.left)
  exact (topRingSheaf R).obj.map V.unop.hom.op a

@[simp]
lemma overScalar_one (U : Opens X) (V : (Over U)ᵒᵖ) :
    overScalar R U V 1 = 1 := by
  change (topRingSheaf R).obj.map V.unop.hom.op 1 = 1
  exact map_one _

@[simp]
lemma overScalar_zero (U : Opens X) (V : (Over U)ᵒᵖ) :
    overScalar R U V 0 = 0 := by
  change (topRingSheaf R).obj.map V.unop.hom.op 0 = 0
  exact map_zero _

lemma overScalar_add (U : Opens X) (V : (Over U)ᵒᵖ)
    (a b : (topRingSheaf R).obj.obj (op U)) :
    overScalar R U V (a + b) = overScalar R U V a + overScalar R U V b := by
  change (topRingSheaf R).obj.map V.unop.hom.op (a + b) = _
  exact map_add _ _ _

lemma overScalar_mul (U : Opens X) (V : (Over U)ᵒᵖ)
    (a b : (topRingSheaf R).obj.obj (op U)) :
    overScalar R U V (a * b) = overScalar R U V a * overScalar R U V b := by
  change (topRingSheaf R).obj.map V.unop.hom.op (a * b) = _
  exact map_mul _ _ _

lemma overScalar_map (U : Opens X) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (a : (topRingSheaf R).obj.obj (op U)) :
    ((topRingSheaf R).over U).obj.map f (overScalar R U V a) =
      overScalar R U W a := by
  change (topRingSheaf R).obj.map f.unop.left.op
      ((topRingSheaf R).obj.map V.unop.hom.op a) =
    (topRingSheaf R).obj.map W.unop.hom.op a
  rw [← ConcreteCategory.comp_apply, ← (topRingSheaf R).obj.map_comp]
  rw [← op_comp, Over.w f.unop]

lemma map_overScalar_smul (P : RingedModules R) (U : Opens X)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (a : (topRingSheaf R).obj.obj (op U)) (m : (P.over U).val.obj V) :
    (P.over U).val.map f (overScalar R U V a • m) =
      overScalar R U W a • (P.over U).val.map f m := by
  simpa only [overScalar_map] using
    (P.over U).val.map_smul f (overScalar R U V a) m

lemma map_overSection_smul (P : RingedModules R) (U : Opens X)
    (W : (Over U)ᵒᵖ) {Z : Opens X} (g : Z ⟶ W.unop.left)
    (a : ((topRingSheaf R).over U).obj.obj W)
    (m : (P.over U).val.obj W) :
    P.val.map g.op (a • m) =
      (topRingSheaf R).obj.map g.op a • P.val.map g.op m := by
  change P.val.map g.op (a • m) =
    (ringSheaf R).obj.map g.op a • P.val.map g.op m
  exact P.val.map_smul g.op a m

def restrictSection (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (m : P.val.obj U) : P.val.obj V :=
  P.val.map f m

@[simp]
lemma restrictSection_add (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (m n : P.val.obj U) :
    restrictSection R P f (m + n) =
      restrictSection R P f m + restrictSection R P f n := by
  exact map_add (P.val.map f).hom m n

lemma restrictSection_smul (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (a : (topRingSheaf R).obj.obj U) (m : P.val.obj U) :
    restrictSection R P f (a • m) =
      (topRingSheaf R).obj.map f a • restrictSection R P f m := by
  change P.val.map f (a • m) =
    (ringSheaf R).obj.map f a • P.val.map f m
  exact P.val.map_smul f a m

lemma restrictSection_comp (P : RingedModules R) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (m : P.val.obj U) :
    restrictSection R P (f ≫ g) m =
      restrictSection R P g (restrictSection R P f m) := by
  exact P.val.map_comp_apply f g m

def overSection (P : RingedModules R) (U : Opens X) (V : (Over U)ᵒᵖ)
    (m : (P.over U).val.obj V) : P.val.obj (op V.unop.left) :=
  m

lemma overSection_injective (P : RingedModules R) (U : Opens X)
    (V : (Over U)ᵒᵖ) : Function.Injective (overSection R P U V) := by
  intro m n h
  exact h

def overRestrictSection (P : RingedModules R) (U : Opens X)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (m : (P.over U).val.obj V) :
    (P.over U).val.obj W :=
  (P.over U).val.map f m

def rebaseOverSection (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (W : (Over V.unop)ᵒᵖ)
    (m : (P.over V.unop).val.obj W) :
    (P.over U.unop).val.obj ((Over.map f.unop).op.obj W) :=
  m

@[simp]
lemma overSection_rebase (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (W : (Over V.unop)ᵒᵖ)
    (m : (P.over V.unop).val.obj W) :
    overSection R P U.unop ((Over.map f.unop).op.obj W)
      (rebaseOverSection R P f W m) = overSection R P V.unop W m :=
  rfl

lemma overSection_restrict (P : RingedModules R) (U : Opens X)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (m : (P.over U).val.obj V) :
    overSection R P U W (overRestrictSection R P U f m) =
      restrictSection R P f.unop.left.op (overSection R P U V m) :=
  rfl

@[simp]
lemma overSection_add (P : RingedModules R) (U : Opens X) (V : (Over U)ᵒᵖ)
    (m n : (P.over U).val.obj V) :
    overSection R P U V (m + n) =
      overSection R P U V m + overSection R P U V n :=
  rfl

lemma overSection_smul (P : RingedModules R) (U : Opens X) (V : (Over U)ᵒᵖ)
    (a : ((topRingSheaf R).over U).obj.obj V)
    (m : (P.over U).val.obj V) :
    overSection R P U V (a • m) =
      (show (topRingSheaf R).obj.obj (op V.unop.left) from a) •
        overSection R P U V m :=
  rfl

lemma overScalar_map_base {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (W : (Over V.unop)ᵒᵖ) (a : (topRingSheaf R).obj.obj U) :
    overScalar R U.unop ((Over.map f.unop).op.obj W) a =
      overScalar R V.unop W ((topRingSheaf R).obj.map f a) := by
  change (topRingSheaf R).obj.map
      ((W.unop.hom ≫ f.unop).op) a =
    (topRingSheaf R).obj.map W.unop.hom.op
      ((topRingSheaf R).obj.map f a)
  rw [op_comp, (topRingSheaf R).obj.map_comp,
    ConcreteCategory.comp_apply]
  simpa

theorem overSMulCommClass (P : RingedModules R) (U : Opens X)
    (V : (Over U)ᵒᵖ) :
    SMulCommClass (((topRingSheaf R).over U).obj.obj V)
      (((topRingSheaf R).over U).obj.obj V) ((P.over U).val.obj V) :=
  ⟨fun a b m => by
    rw [← mul_smul, ← mul_smul]
    congr 1
    change (a * b : R.obj.obj (op V.unop.left)) = b * a
    exact @mul_comm (R.obj.obj (op V.unop.left)) inferInstance a b⟩

private noncomputable def homSmulApp (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U)
    (φ : M.over U.unop ⟶ N.over U.unop) (V : (Over U.unop)ᵒᵖ) :
    (M.over U.unop).val.obj V ⟶ (N.over U.unop).val.obj V := by
  letI := overSMulCommClass R N U.unop V
  exact ConcreteCategory.ofHom (C := ModuleCat _)
    (overScalar R U.unop V a • (φ.val.app V).hom)

private lemma homSmulApp_naturality (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U)
    (φ : M.over U.unop ⟶ N.over U.unop)
    {V W : (Over U.unop)ᵒᵖ} (f : V ⟶ W) :
    (M.over U.unop).val.map f ≫
        (ModuleCat.restrictScalars
          (((topRingSheaf R).over U.unop).obj.map f).hom).map
            (homSmulApp R M N U a φ W) =
      homSmulApp R M N U a φ V ≫ (N.over U.unop).val.map f := by
  ext m
  change overScalar R U.unop W a •
      (φ.val.app W).hom ((M.over U.unop).val.map f m) =
    (N.over U.unop).val.map f
      (overScalar R U.unop V a • (φ.val.app V).hom m)
  rw [PresheafOfModules.naturality_apply]
  exact (map_overScalar_smul R N U.unop f a _).symm

private noncomputable def homSmulVal (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U)
    (φ : M.over U.unop ⟶ N.over U.unop) :
    (M.over U.unop).val ⟶ (N.over U.unop).val where
  app := homSmulApp R M N U a φ
  naturality := homSmulApp_naturality R M N U a φ

noncomputable def homSmul (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U)
    (φ : M.over U.unop ⟶ N.over U.unop) :
    M.over U.unop ⟶ N.over U.unop where
  val := homSmulVal R M N U a φ

noncomputable instance homSMul (U : (Opens X)ᵒᵖ) :
    SMul ((topRingSheaf R).obj.obj U)
      ((homAbPresheaf R M N).obj U) where
  smul := homSmul R M N U

private lemma homModule_one_smul (U : (Opens X)ᵒᵖ)
    (φ : (homAbPresheaf R M N).obj U) : (1 : (topRingSheaf R).obj.obj U) • φ = φ := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V 1 •
    (φ.val.app V).hom m = (φ.val.app V).hom m
  rw [overScalar_one, one_smul]

private lemma homModule_mul_smul (U : (Opens X)ᵒᵖ)
    (a b : (topRingSheaf R).obj.obj U)
    (φ : (homAbPresheaf R M N).obj U) : (a * b) • φ = a • b • φ := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V (a * b) •
    (φ.val.app V).hom m =
      overScalar R U.unop V a •
        (overScalar R U.unop V b • (φ.val.app V).hom m)
  rw [overScalar_mul, mul_smul]

private lemma homModule_smul_zero (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U) :
    a • (0 : (homAbPresheaf R M N).obj U) = 0 := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V a • (0 : (N.over U.unop).val.obj V) = 0
  exact smul_zero _

private lemma homModule_smul_add (U : (Opens X)ᵒᵖ)
    (a : (topRingSheaf R).obj.obj U)
    (φ ψ : (homAbPresheaf R M N).obj U) : a • (φ + ψ) = a • φ + a • ψ := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V a •
    ((φ.val.app V).hom m + (ψ.val.app V).hom m) = _
  exact smul_add _ _ _

private lemma homModule_add_smul (U : (Opens X)ᵒᵖ)
    (a b : (topRingSheaf R).obj.obj U)
    (φ : (homAbPresheaf R M N).obj U) : (a + b) • φ = a • φ + b • φ := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V (a + b) •
    (φ.val.app V).hom m =
      overScalar R U.unop V a • (φ.val.app V).hom m +
        overScalar R U.unop V b • (φ.val.app V).hom m
  rw [overScalar_add, add_smul]

private lemma homModule_zero_smul (U : (Opens X)ᵒᵖ)
    (φ : (homAbPresheaf R M N).obj U) :
    (0 : (topRingSheaf R).obj.obj U) • φ = 0 := by
  apply SheafOfModules.hom_ext
  ext V m
  change overScalar R U.unop V 0 • (φ.val.app V).hom m = 0
  rw [overScalar_zero, zero_smul]

noncomputable instance homModule (U : (Opens X)ᵒᵖ) :
    Module ((topRingSheaf R).obj.obj U)
      ((homAbPresheaf R M N).obj U) where
  one_smul := homModule_one_smul R M N U
  mul_smul := homModule_mul_smul R M N U
  smul_zero := homModule_smul_zero R M N U
  smul_add := homModule_smul_add R M N U
  add_smul := homModule_add_smul R M N U
  zero_smul := homModule_zero_smul R M N U

lemma homRestrict_smul {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (a : (topRingSheaf R).obj.obj U)
    (φ : M.over U.unop ⟶ N.over U.unop) :
    homRestrict R M N f (homSmul R M N U a φ) =
      homSmul R M N V ((topRingSheaf R).obj.map f a)
        (homRestrict R M N f φ) := by
  apply SheafOfModules.hom_ext
  ext W m
  let W' := (Over.map f.unop).op.obj W
  change (topRingSheaf R).obj.map (W.unop.hom ≫ f.unop).op a •
      (show N.val.obj (op W.unop.left) from (φ.val.app W').hom m) =
    (topRingSheaf R).obj.map W.unop.hom.op
        ((topRingSheaf R).obj.map f a) •
      (show N.val.obj (op W.unop.left) from (φ.val.app W').hom m)
  rw [op_comp, (topRingSheaf R).obj.map_comp,
    ConcreteCategory.comp_apply]
  simpa

private lemma homModulePresheaf_map_smul
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (a : (topRingSheaf R).obj.obj U)
    (φ : (homAbPresheaf R M N).obj U) :
    (homAbPresheaf R M N).map f (a • φ) =
      (topRingSheaf R).obj.map f a •
        (homAbPresheaf R M N).map f φ := by
  change homRestrict R M N f (homSmul R M N U a φ) =
    homSmul R M N V ((topRingSheaf R).obj.map f a)
      (homRestrict R M N f φ)
  exact homRestrict_smul R M N f a φ

noncomputable def homModulePresheaf :
    PresheafOfModules (topRingSheaf R).obj :=
  PresheafOfModules.ofPresheaf (homAbPresheaf R M N)
    (map_smul := fun {U V} f a φ =>
      homModulePresheaf_map_smul R M N (U := U) (V := V) f a φ)

abbrev additiveSheaf (M : RingedModules R) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (topRingSheaf R)).obj M

def homToSheafHomApp (U : (Opens X)ᵒᵖ)
    (φ : M.over U.unop ⟶ N.over U.unop) :
    (CategoryTheory.sheafHom (additiveSheaf R M) (additiveSheaf R N)).obj.obj U :=
  (SheafOfModules.toSheaf ((topRingSheaf R).over U.unop)).map φ

private lemma homToSheafHomApp_naturality {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) :
    (homAbPresheaf R M N ⋙ forget AddCommGrpCat.{u}).map f ≫
        ↾homToSheafHomApp R M N V =
      ↾homToSheafHomApp R M N U ≫
        (CategoryTheory.sheafHom
          (additiveSheaf R M) (additiveSheaf R N)).obj.map f := by
  ext φ W w
  rfl

private def homToSheafHomAppHom (U : (Opens X)ᵒᵖ) :
    (homAbPresheaf R M N ⋙ forget AddCommGrpCat.{u}).obj U ⟶
      (CategoryTheory.sheafHom
        (additiveSheaf R M) (additiveSheaf R N)).obj.obj U :=
  ↾homToSheafHomApp R M N U

private lemma homToSheafHom_naturality {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) :
    (homAbPresheaf R M N ⋙ forget AddCommGrpCat.{u}).map f ≫
        homToSheafHomAppHom R M N V =
      homToSheafHomAppHom R M N U ≫
        (CategoryTheory.sheafHom
          (additiveSheaf R M) (additiveSheaf R N)).obj.map f :=
  homToSheafHomApp_naturality R M N f

def homToSheafHom :
    homAbPresheaf R M N ⋙ forget AddCommGrpCat.{u} ⟶
      (CategoryTheory.sheafHom (additiveSheaf R M) (additiveSheaf R N)).obj where
  app := homToSheafHomAppHom R M N
  naturality := fun {U V} f =>
    homToSheafHom_naturality R M N (U := U) (V := V) f

lemma homToSheafHomApp_injective (U : (Opens X)ᵒᵖ) :
    Function.Injective (homToSheafHomApp R M N U) := by
  intro φ ψ h
  exact (SheafOfModules.toSheaf ((topRingSheaf R).over U.unop)).map_injective h

abbrev linearHomRange : Subfunctor
    (CategoryTheory.sheafHom (additiveSheaf R M) (additiveSheaf R N)).obj :=
  Subfunctor.range (homToSheafHom R M N)

lemma linearHomRange_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (linearHomRange R M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff
    (G := linearHomRange R M N)
    ((isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X)
      (CategoryTheory.sheafHom
        (additiveSheaf R M) (additiveSheaf R N)).obj).1
      (CategoryTheory.sheafHom
        (additiveSheaf R M) (additiveSheaf R N)).property)).2
  intro U s hs
  have hlinear : ∀ (W : (Over U.unop)ᵒᵖ)
      (a : ((topRingSheaf R).over U.unop).obj.obj W)
      (m : (M.over U.unop).val.obj W),
      (show (N.over U.unop).val.obj W from s.hom.app W (a • m)) =
        a • (show (N.over U.unop).val.obj W from s.hom.app W m) := by
    intro W a m
    apply N.isSheaf.isSeparated _ _
      ((Opens.grothendieckTopology X).pullback_stable W.unop.hom hs)
    intro Z g hg
    change (linearHomRange R M N).sieveOfSection s (g ≫ W.unop.hom) at hg
    rcases hg with ⟨φZ, hφZ⟩
    let q : Over.mk (g ≫ W.unop.hom) ⟶ W.unop := Over.homMk g
    have hsNat (x : (M.over U.unop).val.obj W) :
        s.hom.app (op (Over.mk (g ≫ W.unop.hom))) (M.val.map g.op x) =
          N.val.map g.op (s.hom.app W x) := by
      exact CategoryTheory.congr_fun (s.hom.naturality q.op) x
    have hφZ' := congrArg
      (fun t => t.hom.app (op (Over.mk (𝟙 Z)))) hφZ
    dsimp [homToSheafHomApp] at hφZ'
    have hφZ_apply (x : M.val.obj (op Z)) :
        φZ.val.app (op (Over.mk (𝟙 Z))) x =
          s.hom.app (op (Over.mk (g ≫ W.unop.hom))) x := by
      exact CategoryTheory.congr_fun hφZ' x
    change N.val.map g.op (s.hom.app W (a • m)) =
      N.val.map g.op
        (a • (show (N.over U.unop).val.obj W from s.hom.app W m))
    rw [← hsNat (a • m)]
    rw [map_overSection_smul R M U.unop W g a m]
    erw [← hφZ_apply]
    erw [(φZ.val.app (op (Over.mk (𝟙 Z)))).hom.map_smul]
    erw [hφZ_apply]
    rw [map_overSection_smul R N U.unop W g a
      (show (N.over U.unop).val.obj W from s.hom.app W m)]
    erw [hsNat m]
    rfl
  let φ : M.over U.unop ⟶ N.over U.unop :=
    ⟨PresheafOfModules.homMk s.hom hlinear⟩
  exact ⟨φ, rfl⟩

lemma homAbPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (homAbPresheaf R M N) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget
    (Opens.grothendieckTopology X) (homAbPresheaf R M N)
      (forget AddCommGrpCat.{u})).2
  let p := homToSheafHom R M N
  letI (U : (Opens X)ᵒᵖ) : Mono (p.app U) :=
    (mono_iff_injective _).2 (homToSheafHomApp_injective R M N U)
  letI : Mono p := NatTrans.mono_of_mono_app p
  exact (Presheaf.isSheaf_of_iso_iff
    (asIso (Subfunctor.toRange p))).2 (linearHomRange_isSheaf R M N)

noncomputable def internalHom : RingedModules R where
  val := homModulePresheaf R M N
  isSheaf := homAbPresheaf_isSheaf R M N

private def currySectionToFun {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (n : (N.over U.unop).val.obj V) : (P.over U.unop).val.obj V :=
  f.app (op V.unop.left)
    (tensorPure R M N (op V.unop.left)
      (restrictSection R M V.unop.hom.op m)
      (overSection R N U.unop V n))

private lemma currySectionToFun_add {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (n n' : (N.over U.unop).val.obj V) :
    currySectionToFun R M N f U m V (n + n') =
      currySectionToFun R M N f U m V n +
        currySectionToFun R M N f U m V n' := by
  change f.app _ (tensorPure R M N _
      (restrictSection R M V.unop.hom.op m)
      (overSection R N U.unop V (n + n'))) =
    f.app _ (tensorPure R M N _
        (restrictSection R M V.unop.hom.op m)
        (overSection R N U.unop V n)) +
      f.app _ (tensorPure R M N _
        (restrictSection R M V.unop.hom.op m)
        (overSection R N U.unop V n'))
  rw [overSection_add]
  exact map_tensorPure_add_right.{u, u, u}
    (R := R) (M := M) (N := N) f _ _ _ _

private lemma currySectionToFun_smul {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (a : ((topRingSheaf R).over U.unop).obj.obj V)
    (n : (N.over U.unop).val.obj V) :
    currySectionToFun R M N f U m V (a • n) =
      a • currySectionToFun R M N f U m V n := by
  change f.app _ (tensorPure R M N _
      (restrictSection R M V.unop.hom.op m)
      (overSection R N U.unop V (a • n))) =
    (show (topRingSheaf R).obj.obj (op V.unop.left) from a) •
      f.app _ (tensorPure R M N _
        (restrictSection R M V.unop.hom.op m)
        (overSection R N U.unop V n))
  rw [overSection_smul]
  exact map_tensorPure_smul_right.{u, u, u}
    (R := R) (M := M) (N := N) f _ _ _ _

private noncomputable def currySectionApp {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ) :
    (N.over U.unop).val.obj V ⟶ (P.over U.unop).val.obj V :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun := currySectionToFun R M N f U m V
      map_add' := currySectionToFun_add R M N f U m V
      map_smul' := currySectionToFun_smul R M N f U m V }

private lemma currySectionApp_naturality {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) {V W : (Over U.unop)ᵒᵖ} (q : V ⟶ W) :
    (N.over U.unop).val.map q ≫
        (ModuleCat.restrictScalars
          (((topRingSheaf R).over U.unop).obj.map q).hom).map
            (currySectionApp R M N f U m W) =
      currySectionApp R M N f U m V ≫ (P.over U.unop).val.map q := by
  ext n
  change f.app _ (tensorPure R M N (op W.unop.left)
        (restrictSection R M W.unop.hom.op m)
        (overSection R N U.unop W (overRestrictSection R N U.unop q n))) =
    P.val.map q.unop.left.op
      (f.app _ (tensorPure R M N (op V.unop.left)
        (restrictSection R M V.unop.hom.op m)
        (overSection R N U.unop V n)))
  rw [overSection_restrict]
  rw [← PresheafOfModules.naturality_apply f]
  rw [tensorPure_map.{u, u, u} R M N]
  congr 2
  change restrictSection R M W.unop.hom.op m =
    restrictSection R M q.unop.left.op
      (restrictSection R M V.unop.hom.op m)
  have h : W.unop.hom.op = V.unop.hom.op ≫ q.unop.left.op := by
    rw [← op_comp, Over.w q.unop]
  rw [h, restrictSection_comp]

private noncomputable def currySectionVal {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) : (N.over U.unop).val ⟶ (P.over U.unop).val where
  app := currySectionApp R M N f U m
  naturality := currySectionApp_naturality R M N f U m

noncomputable def currySection {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) : N.over U.unop ⟶ P.over U.unop where
  val := currySectionVal R M N f U m

@[simp]
lemma currySection_apply {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (n : (N.over U.unop).val.obj V) :
    (currySection R M N f U m).val.app V n =
      f.app (op V.unop.left)
        (tensorPure R M N (op V.unop.left)
          (restrictSection R M V.unop.hom.op m)
          (overSection R N U.unop V n)) :=
  rfl

@[simp]
lemma overSection_currySection_apply {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ)
    (n : (N.over U.unop).val.obj V) :
    overSection R P U.unop V ((currySection R M N f U m).val.app V n) =
      f.app (op V.unop.left)
        (tensorPure R M N (op V.unop.left)
          (restrictSection R M V.unop.hom.op m)
          (overSection R N U.unop V n)) :=
  rfl

private lemma currySection_add {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) :
    ∀ (U : (Opens X)ᵒᵖ) (m m' : M.val.obj U),
      currySection R M N f U (m + m') =
        currySection R M N f U m + currySection R M N f U m' := by
  intro U m m'
  apply SheafOfModules.hom_ext
  ext V n
  change (currySection R M N f U (m + m')).val.app V n =
    (currySection R M N f U m).val.app V n +
      (currySection R M N f U m').val.app V n
  rw [currySection_apply, currySection_apply, currySection_apply,
    restrictSection_add]
  exact map_tensorPure_add_left.{u, u, u}
    (R := R) (M := M) (N := N) f _ _ _ _

private lemma currySection_smul {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) :
    ∀ (U : (Opens X)ᵒᵖ) (a : (topRingSheaf R).obj.obj U)
      (m : M.val.obj U),
      currySection R M N f U (a • m) =
        homSmul R N P U a (currySection R M N f U m) := by
  intro U a m
  apply SheafOfModules.hom_ext
  ext V n
  change (currySection R M N f U (a • m)).val.app V n =
    overScalar R U.unop V a • (currySection R M N f U m).val.app V n
  rw [currySection_apply, currySection_apply, restrictSection_smul]
  exact map_tensorPure_smul_left.{u, u, u}
    (R := R) (M := M) (N := N) f _ _ _ _

private noncomputable def curryHomApp {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ) :
    M.val.obj U ⟶ (internalHom R N P).val.obj U :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun := currySection R M N f U
      map_add' := currySection_add R M N f U
      map_smul' := currySection_smul R M N f U }

private lemma curryHomApp_naturality {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) {U V : (Opens X)ᵒᵖ}
    (q : U ⟶ V) :
    M.val.map q ≫
        (ModuleCat.restrictScalars ((topRingSheaf R).obj.map q).hom).map
          (curryHomApp R M N f V) =
      curryHomApp R M N f U ≫ (internalHom R N P).val.map q := by
  ext m
  change currySection R M N f V (restrictSection R M q m) =
    homRestrict R N P q (currySection R M N f U m)
  apply SheafOfModules.hom_ext
  ext W n
  change overSection R P V.unop W
      ((currySection R M N f V (restrictSection R M q m)).val.app W n) =
    overSection R P U.unop ((Over.map q.unop).op.obj W)
      ((currySection R M N f U m).val.app
        ((Over.map q.unop).op.obj W) (rebaseOverSection R N q W n))
  rw [overSection_currySection_apply, overSection_currySection_apply]
  rw [overSection_rebase]
  congr 2
  rw [← restrictSection_comp]
  rfl

private noncomputable def curryHomVal {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) :
    M.val ⟶ (internalHom R N P).val where
  app := curryHomApp R M N f
  naturality := curryHomApp_naturality R M N f

noncomputable def curryHom {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) :
    M ⟶ internalHom R N P where
  val := curryHomVal R M N f

def internalHomEval (N P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (φ : N.over U.unop ⟶ P.over U.unop) (n : N.val.obj U) :
    P.val.obj U :=
  φ.val.app (op (Over.mk (𝟙 U.unop))) n

def nativeSection (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (m : (directPresheaf R P).obj U) : P.val.obj U :=
  m

def nativeScalar (U : (Opens X)ᵒᵖ) (a : R.obj.obj U) :
    (topRingSheaf R).obj.obj U :=
  a

lemma nativeSection_smul_top (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (a : R.obj.obj U) (m : (directPresheaf R P).obj U) :
    (show (P.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
      nativeSection R P U (a • m)) =
      overScalar R U.unop (op (Over.mk (𝟙 U.unop))) (nativeScalar R U a) •
        (show (P.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
          nativeSection R P U m) := by
  change nativeScalar R U a • nativeSection R P U m =
    (topRingSheaf R).obj.map (𝟙 U.unop).op (nativeScalar R U a) •
      nativeSection R P U m
  simp only [op_id]
  have h := CategoryTheory.congr_fun ((topRingSheaf R).obj.map_id U)
    (nativeScalar R U a)
  rw [h]
  change nativeScalar R U a • nativeSection R P U m =
    nativeScalar R U a • nativeSection R P U m
  rfl

def nativeHomSection (N P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (φ : (directPresheaf R (internalHom R N P)).obj U) :
    N.over U.unop ⟶ P.over U.unop :=
  φ

def directInternalHomEval (N P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (φ : (directPresheaf R (internalHom R N P)).obj U)
    (n : (directPresheaf R N).obj U) : (directPresheaf R P).obj U :=
  overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
    ((nativeHomSection R N P U φ).val.app
      (op (Over.mk (𝟙 U.unop)))
        (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
          nativeSection R N U n))

lemma directInternalHomEval_add_left (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (φ ψ : (directPresheaf R (internalHom R N P)).obj U)
    (n : (directPresheaf R N).obj U) :
    directInternalHomEval R N P U (φ + ψ) n =
      directInternalHomEval R N P U φ n + directInternalHomEval R N P U ψ n :=
  rfl

lemma directInternalHomEval_smul_left (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (a : R.obj.obj U) (φ : (directPresheaf R (internalHom R N P)).obj U)
    (n : (directPresheaf R N).obj U) :
    directInternalHomEval R N P U (a • φ) n =
      a • directInternalHomEval R N P U φ n := by
  change overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
      (overScalar R U.unop (op (Over.mk (𝟙 U.unop))) (nativeScalar R U a) •
        (nativeHomSection R N P U φ).val.app
          (op (Over.mk (𝟙 U.unop)))
            (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
              nativeSection R N U n)) =
    nativeScalar R U a • overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
      ((nativeHomSection R N P U φ).val.app
        (op (Over.mk (𝟙 U.unop)))
          (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
            nativeSection R N U n))
  rw [overSection_smul]
  change (topRingSheaf R).obj.map (𝟙 U.unop).op (nativeScalar R U a) • _ = _
  simp only [op_id]
  have h := CategoryTheory.congr_fun ((topRingSheaf R).obj.map_id U)
    (nativeScalar R U a)
  rw [h]
  change nativeScalar R U a • _ = nativeScalar R U a • _
  rfl

lemma directInternalHomEval_add_right (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (φ : (directPresheaf R (internalHom R N P)).obj U)
    (n n' : (directPresheaf R N).obj U) :
    directInternalHomEval R N P U φ (n + n') =
      directInternalHomEval R N P U φ n + directInternalHomEval R N P U φ n' := by
  exact map_add
    ((nativeHomSection R N P U φ).val.app
      (op (Over.mk (𝟙 U.unop)))).hom _ _

lemma directInternalHomEval_smul_right (P : RingedModules R) (U : (Opens X)ᵒᵖ)
    (a : R.obj.obj U) (φ : (directPresheaf R (internalHom R N P)).obj U)
    (n : (directPresheaf R N).obj U) :
    directInternalHomEval R N P U φ (a • n) =
      a • directInternalHomEval R N P U φ n := by
  unfold directInternalHomEval
  change overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
      ((nativeHomSection R N P U φ).val.app
        (op (Over.mk (𝟙 U.unop)))
          (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
            nativeSection R N U (a • n))) =
    nativeScalar R U a • overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
      ((nativeHomSection R N P U φ).val.app
        (op (Over.mk (𝟙 U.unop)))
          (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
            nativeSection R N U n))
  rw [nativeSection_smul_top]
  rw [map_smul]
  rw [overSection_smul]
  change (topRingSheaf R).obj.map (𝟙 U.unop).op (nativeScalar R U a) • _ = _
  simp only [op_id]
  have h := CategoryTheory.congr_fun ((topRingSheaf R).obj.map_id U)
    (nativeScalar R U a)
  rw [h]
  change nativeScalar R U a • _ = nativeScalar R U a • _
  rfl

lemma directInternalHomEval_map (P : RingedModules R) {U V : (Opens X)ᵒᵖ}
    (q : U ⟶ V) (φ : (directPresheaf R (internalHom R N P)).obj U)
    (n : (directPresheaf R N).obj U) :
    (directPresheaf R P).map q (directInternalHomEval R N P U φ n) =
      directInternalHomEval R N P V
        ((directPresheaf R (internalHom R N P)).map q φ)
        ((directPresheaf R N).map q n) := by
  change P.val.map q
      (internalHomEval R N P U (nativeHomSection R N P U φ)
        (nativeSection R N U n)) =
    internalHomEval R N P V
      (homRestrict R N P q (nativeHomSection R N P U φ))
      (N.val.map q (nativeSection R N U n))
  have h := CategoryTheory.congr_fun
    ((nativeHomSection R N P U φ).val.naturality
      (Over.homMk q.unop : Over.mk q.unop ⟶ Over.mk (𝟙 U.unop)).op)
    (nativeSection R N U n)
  have h' := congrArg
    (overSection R P U.unop (op (Over.mk q.unop))) h
  exact h'.symm

private def uncurryPair {P : RingedModules R}
    (g : M ⟶ internalHom R N P) :
    ∀ (U : (Opens X)ᵒᵖ), (directPresheaf R M).obj U →
      (directPresheaf R N).obj U → (directPresheaf R P).obj U :=
  fun U m n => directInternalHomEval R N P U ((directHom R g).app U m) n

private lemma uncurryPair_add_left {P : RingedModules R}
    (g : M ⟶ internalHom R N P) (U : (Opens X)ᵒᵖ)
    (m m' : (directPresheaf R M).obj U)
    (n : (directPresheaf R N).obj U) :
    uncurryPair R M N g U (m + m') n =
      uncurryPair R M N g U m n + uncurryPair R M N g U m' n := by
  unfold uncurryPair
  rw [map_add ((directHom R g).app U).hom]
  exact directInternalHomEval_add_left R N P U _ _ _

private lemma uncurryPair_smul_left {P : RingedModules R}
    (g : M ⟶ internalHom R N P) (U : (Opens X)ᵒᵖ)
    (a : R.obj.obj U) (m : (directPresheaf R M).obj U)
    (n : (directPresheaf R N).obj U) :
    uncurryPair R M N g U (a • m) n = a • uncurryPair R M N g U m n := by
  unfold uncurryPair
  rw [map_smul ((directHom R g).app U).hom]
  exact directInternalHomEval_smul_left R N P U _ _ _

private lemma uncurryPair_add_right {P : RingedModules R}
    (g : M ⟶ internalHom R N P) (U : (Opens X)ᵒᵖ)
    (m : (directPresheaf R M).obj U)
    (n n' : (directPresheaf R N).obj U) :
    uncurryPair R M N g U m (n + n') =
      uncurryPair R M N g U m n + uncurryPair R M N g U m n' :=
  directInternalHomEval_add_right R N P U _ _ _

private lemma uncurryPair_smul_right {P : RingedModules R}
    (g : M ⟶ internalHom R N P) (U : (Opens X)ᵒᵖ)
    (a : R.obj.obj U) (m : (directPresheaf R M).obj U)
    (n : (directPresheaf R N).obj U) :
    uncurryPair R M N g U m (a • n) = a • uncurryPair R M N g U m n :=
  directInternalHomEval_smul_right R N P U _ _ _

private noncomputable def uncurryPresheafApp {P : RingedModules R}
    (g : M ⟶ internalHom R N P) (U : (Opens X)ᵒᵖ) :
    (tensorPresheaf R M N).obj U ⟶ P.val.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (uncurryPair R M N g U)
    (uncurryPair_add_left R M N g U)
    (uncurryPair_smul_left R M N g U)
    (uncurryPair_add_right R M N g U)
    (uncurryPair_smul_right R M N g U)

private lemma uncurryPresheafApp_naturality {P : RingedModules R}
    (g : M ⟶ internalHom R N P) {U V : (Opens X)ᵒᵖ} (q : U ⟶ V) :
    (tensorPresheaf R M N).map q ≫
        (ModuleCat.restrictScalars ((topRingSheaf R).obj.map q).hom).map
          (uncurryPresheafApp R M N g V) =
      uncurryPresheafApp R M N g U ≫ P.val.map q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change directInternalHomEval R N P V
      ((directHom R g).app V ((directPresheaf R M).map q m))
      ((directPresheaf R N).map q n) =
    (directPresheaf R P).map q
      (directInternalHomEval R N P U ((directHom R g).app U m) n)
  rw [PresheafOfModules.naturality_apply (directHom R g)]
  exact (directInternalHomEval_map R N P q _ _).symm

noncomputable def uncurryPresheaf {P : RingedModules R}
    (g : M ⟶ internalHom R N P) :
    tensorPresheaf R M N ⟶ P.val where
  app := uncurryPresheafApp R M N g
  naturality := uncurryPresheafApp_naturality R M N g

private lemma tensorInternalHom_left_inv (P : RingedModules R)
    (f : tensorObj R M N ⟶ P) :
    tensorLift R
        (uncurryPresheaf R M N
          (curryHom R M N (tensorHomEquiv R M N P f))) = f := by
  apply (tensorHomEquiv R M N P).injective
  rw [tensorHomEquiv_tensorLift.{u, u, u}
    (R := R) (M := M) (N := N) (P := P)]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  let F : tensorPresheaf R M N ⟶ P.val := tensorHomEquiv R M N P f
  change directInternalHomEval R N P U
      ((directHom R (curryHom R M N F)).app U m) n =
    F.app U (tensorPure R M N U
      (nativeSection R M U m) (nativeSection R N U n))
  change overSection R P U.unop (op (Over.mk (𝟙 U.unop)))
      ((currySection R M N F U (nativeSection R M U m)).val.app
        (op (Over.mk (𝟙 U.unop)))
          (show (N.over U.unop).val.obj (op (Over.mk (𝟙 U.unop))) from
            nativeSection R N U n)) = _
  rw [overSection_currySection_apply]
  congr 2
  change M.val.map (𝟙 U.unop).op (nativeSection R M U m) =
    nativeSection R M U m
  simp only [op_id]
  have h := CategoryTheory.congr_fun (M.val.map_id U) (nativeSection R M U m)
  exact h.trans (by rfl)

private lemma tensorInternalHom_right_inv (P : RingedModules R)
    (g : M ⟶ internalHom R N P) :
    curryHom R M N
      (tensorHomEquiv R M N P
        (tensorLift R (uncurryPresheaf R M N g))) = g := by
  rw [tensorHomEquiv_tensorLift.{u, u, u}
    (R := R) (M := M) (N := N) (P := P)]
  apply SheafOfModules.hom_ext
  ext U m
  apply SheafOfModules.hom_ext
  ext V n
  change internalHomEval R N P (op V.unop.left)
      (g.val.app (op V.unop.left) (M.val.map V.unop.hom.op m)) n =
    (g.val.app U m).val.app V n
  have hg := PresheafOfModules.naturality_apply g.val V.unop.hom.op m
  change g.val.app (op V.unop.left) (M.val.map V.unop.hom.op m) =
    homRestrict R N P V.unop.hom.op (g.val.app U m) at hg
  rw [hg]
  rfl

private noncomputable def tensorInternalHomToFun (P : RingedModules R)
    (f : tensorObj R M N ⟶ P) : M ⟶ internalHom R N P :=
  curryHom R M N (tensorHomEquiv R M N P f)

private noncomputable def tensorInternalHomInvFun (P : RingedModules R)
    (g : M ⟶ internalHom R N P) : tensorObj R M N ⟶ P :=
  tensorLift R (uncurryPresheaf R M N g)

noncomputable def tensorInternalHomEquiv (P : RingedModules R) :
    (tensorObj R M N ⟶ P) ≃ (M ⟶ internalHom R N P) where
  toFun := tensorInternalHomToFun R M N P
  invFun := tensorInternalHomInvFun R M N P
  left_inv := tensorInternalHom_left_inv R M N P
  right_inv := tensorInternalHom_right_inv R M N P

private def internalHomMapToFun {P Q : RingedModules R} (h : P ⟶ Q)
    (U : (Opens X)ᵒᵖ) (φ : N.over U.unop ⟶ P.over U.unop) :
    N.over U.unop ⟶ Q.over U.unop :=
  φ ≫ h.over U.unop

private lemma internalHomMapToFun_add {P Q : RingedModules R} (h : P ⟶ Q)
    (U : (Opens X)ᵒᵖ) (φ ψ : N.over U.unop ⟶ P.over U.unop) :
    internalHomMapToFun R N h U (φ + ψ) =
      internalHomMapToFun R N h U φ + internalHomMapToFun R N h U ψ :=
  Preadditive.add_comp _ _ _ φ ψ (h.over U.unop)

private lemma internalHomMapToFun_smul {P Q : RingedModules R} (h : P ⟶ Q)
    (U : (Opens X)ᵒᵖ) (a : (topRingSheaf R).obj.obj U)
    (φ : N.over U.unop ⟶ P.over U.unop) :
    internalHomMapToFun R N h U (homSmul R N P U a φ) =
      homSmul R N Q U a (internalHomMapToFun R N h U φ) := by
  apply SheafOfModules.hom_ext
  ext V n
  change (h.over U.unop).val.app V
      (overScalar R U.unop V a • φ.val.app V n) =
    overScalar R U.unop V a •
      (h.over U.unop).val.app V (φ.val.app V n)
  exact map_smul ((h.over U.unop).val.app V).hom _ _

private noncomputable def internalHomMapApp {P Q : RingedModules R}
    (h : P ⟶ Q) (U : (Opens X)ᵒᵖ) :
    (internalHom R N P).val.obj U ⟶ (internalHom R N Q).val.obj U :=
  ModuleCat.ofHom
    { toFun := internalHomMapToFun R N h U
      map_add' := internalHomMapToFun_add R N h U
      map_smul' := internalHomMapToFun_smul R N h U }

private lemma internalHomMapApp_naturality {P Q : RingedModules R}
    (h : P ⟶ Q) {U V : (Opens X)ᵒᵖ} (q : U ⟶ V) :
    (internalHom R N P).val.map q ≫
        (ModuleCat.restrictScalars ((topRingSheaf R).obj.map q).hom).map
          (internalHomMapApp R N h V) =
      internalHomMapApp R N h U ≫ (internalHom R N Q).val.map q := by
  ext φ W n
  rfl

private noncomputable def internalHomMapVal {P Q : RingedModules R}
    (h : P ⟶ Q) : (internalHom R N P).val ⟶ (internalHom R N Q).val where
  app := internalHomMapApp R N h
  naturality := internalHomMapApp_naturality R N h

noncomputable def internalHomMap {P Q : RingedModules R} (h : P ⟶ Q) :
    internalHom R N P ⟶ internalHom R N Q where
  val := internalHomMapVal R N h

@[simp]
lemma internalHomMap_id (P : RingedModules R) :
    internalHomMap R N (𝟙 P) = 𝟙 (internalHom R N P) := by
  apply SheafOfModules.hom_ext
  ext U φ V n
  rfl

@[simp]
lemma internalHomMap_comp {P Q S : RingedModules R} (f : P ⟶ Q) (g : Q ⟶ S) :
    internalHomMap R N (f ≫ g) =
      internalHomMap R N f ≫ internalHomMap R N g := by
  apply SheafOfModules.hom_ext
  ext U φ V n
  rfl

private noncomputable def tensorRightFunctorObj
    (M : RingedModules R) : RingedModules R :=
  tensorObj R M N

private noncomputable def tensorRightFunctorMap
    {M M' : RingedModules R} (f : M ⟶ M') :
    tensorRightFunctorObj R N M ⟶ tensorRightFunctorObj R N M' :=
  tensorHom R f (𝟙 N)

noncomputable def tensorRightFunctor : RingedModules R ⥤ RingedModules R where
  obj := tensorRightFunctorObj R N
  map := tensorRightFunctorMap R N
  map_id M := tensorHom_id R M N
  map_comp f g := tensorHom_comp R f g (𝟙 N) (𝟙 N)

private noncomputable def internalHomFunctorObj
    (P : RingedModules R) : RingedModules R :=
  internalHom R N P

private noncomputable def internalHomFunctorMap
    {P Q : RingedModules R} (h : P ⟶ Q) :
    internalHomFunctorObj R N P ⟶ internalHomFunctorObj R N Q :=
  internalHomMap R N h

noncomputable def internalHomFunctor : RingedModules R ⥤ RingedModules R where
  obj := internalHomFunctorObj R N
  map := internalHomFunctorMap R N
  map_id := internalHomMap_id R N
  map_comp := internalHomMap_comp R N

lemma tensorHomEquiv_apply {P : RingedModules R}
    (f : tensorObj R M N ⟶ P) :
    tensorHomEquiv R M N P f = tensorUnit R M N ≫ f.val := by
  rfl

lemma tensorLift_tmul {P : RingedModules R}
    (f : tensorPresheaf R M N ⟶ P.val) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (tensorLift R f).val.app U (tmul R M N U m n) =
      f.app U (tensorPure R M N U m n) := by
  have h := tensorHomEquiv_tensorLift R f
  rw [tensorHomEquiv_apply] at h
  have hU := congrArg (fun q => q.app U) h
  exact CategoryTheory.congr_fun hU (tensorPure R M N U m n)

lemma tensorInternalHomEquiv_naturality_right {P Q : RingedModules R}
    (f : tensorObj R M N ⟶ P) (g : P ⟶ Q) :
    tensorInternalHomEquiv R M N Q (f ≫ g) =
      tensorInternalHomEquiv R M N P f ≫ internalHomMap R N g := by
  let Ffg : tensorPresheaf R M N ⟶ Q.val := tensorHomEquiv R M N Q (f ≫ g)
  let Ff : tensorPresheaf R M N ⟶ P.val := tensorHomEquiv R M N P f
  change curryHom R M N Ffg = curryHom R M N Ff ≫ internalHomMap R N g
  apply SheafOfModules.hom_ext
  ext U m
  apply SheafOfModules.hom_ext
  ext V n
  change overSection R Q U.unop V
      ((currySection R M N Ffg U m).val.app V n) =
    overSection R Q U.unop V
      (((currySection R M N Ff U m ≫ g.over U.unop).val.app V) n)
  rw [overSection_currySection_apply]
  change Ffg.app (op V.unop.left)
      (tensorPure R M N (op V.unop.left)
        (restrictSection R M V.unop.hom.op m)
        (overSection R N U.unop V n)) =
    g.val.app (op V.unop.left)
      (Ff.app (op V.unop.left)
        (tensorPure R M N (op V.unop.left)
          (restrictSection R M V.unop.hom.op m)
          (overSection R N U.unop V n)))
  rfl

lemma tensorInternalHomEquiv_naturality_left_symm {L P : RingedModules R}
    (a : L ⟶ M) (g : M ⟶ internalHom R N P) :
    (tensorInternalHomEquiv R L N P).symm (a ≫ g) =
      tensorHom R a (𝟙 N) ≫
        (tensorInternalHomEquiv R M N P).symm g := by
  change tensorLift R (uncurryPresheaf R L N (a ≫ g)) =
    tensorHom R a (𝟙 N) ≫ tensorLift R (uncurryPresheaf R M N g)
  apply (tensorHomEquiv R L N P).injective
  rw [tensorHomEquiv_tensorLift.{u, u, u}
    (R := R) (M := L) (N := N) (P := P), tensorHomEquiv_apply]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change directInternalHomEval R N P U ((directHom R (a ≫ g)).app U m) n =
    (tensorLift R (uncurryPresheaf R M N g)).val.app U
      ((tensorHom R a (𝟙 N)).val.app U
        (tmul R L N U (nativeSection R L U m) (nativeSection R N U n)))
  rw [tensorHom_tmul.{u, u, u}, tensorLift_tmul]
  rfl

private noncomputable def tensorHomCoreEquiv
    (M P : RingedModules R) :
    ((tensorRightFunctor R N).obj M ⟶ P) ≃
      (M ⟶ (internalHomFunctor R N).obj P) :=
  tensorInternalHomEquiv R M N P

private lemma tensorHomCoreEquiv_naturality_left_symm
    {L M P : RingedModules R} (f : L ⟶ M)
    (g : M ⟶ (internalHomFunctor R N).obj P) :
    (tensorHomCoreEquiv R N L P).symm (f ≫ g) =
      (tensorRightFunctor R N).map f ≫
        (tensorHomCoreEquiv R N M P).symm g :=
  tensorInternalHomEquiv_naturality_left_symm R M N f g

private lemma tensorHomCoreEquiv_naturality_right
    {M P Q : RingedModules R}
    (f : (tensorRightFunctor R N).obj M ⟶ P) (g : P ⟶ Q) :
    tensorHomCoreEquiv R N M Q (f ≫ g) =
      tensorHomCoreEquiv R N M P f ≫
        (internalHomFunctor R N).map g :=
  tensorInternalHomEquiv_naturality_right R M N f g

private noncomputable def tensorHomCoreHomEquiv :
    Adjunction.CoreHomEquiv (tensorRightFunctor R N)
      (internalHomFunctor R N) where
  homEquiv := tensorHomCoreEquiv R N
  homEquiv_naturality_left_symm :=
    tensorHomCoreEquiv_naturality_left_symm R N
  homEquiv_naturality_right := tensorHomCoreEquiv_naturality_right R N

noncomputable def tensorHomAdjunction :
    tensorRightFunctor R N ⊣ internalHomFunctor R N :=
  Adjunction.mkOfHomEquiv (tensorHomCoreHomEquiv R N)

end

end LSZ.CommRingSheaf
