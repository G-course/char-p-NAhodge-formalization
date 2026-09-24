import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Tensor products of sheaves of modules

This file defines the tensor product over an arbitrary sheaf of commutative
rings.  Consequently the construction belongs to ringed spaces, not to
schemes.  It is obtained by sheafifying the objectwise tensor product of the
underlying presheaves of modules.
-/

open CategoryTheory Limits Opposite
open scoped MonoidalCategory TensorProduct

namespace LSZ

universe u v₁ u₁

noncomputable section

namespace CommRingSheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- Regard a sheaf of commutative rings as a sheaf of rings using mathlib's
canonical sheaf-composition functor.  Thus, for a scheme structure sheaf,
this is definitionally `Scheme.ringCatSheaf`. -/
abbrev ringSheaf : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- Sheaves of modules over a sheaf of commutative rings. -/
abbrev Modules := SheafOfModules.{u} (ringSheaf R)

section

/-- Rewrite a module presheaf over the canonical forgotten ring sheaf as a
module presheaf over the visibly composed commutative-ring presheaf.  The
underlying data is unchanged. -/
abbrev directPresheaf (M : Modules R) :
    PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
  M.val

/-- The same identity rewrite on morphisms. -/
noncomputable def directHom {M N : Modules R} (f : M ⟶ N) :
    directPresheaf R M ⟶ directPresheaf R N := by
  exact f.val

/-- The objectwise tensor-product presheaf underlying the tensor product of
module sheaves. -/
noncomputable def tensorPresheaf (M N : Modules R) :
    PresheafOfModules (ringSheaf R).obj := by
  change PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat.{u})
  exact directPresheaf R M ⊗ directPresheaf R N

/-- A pure tensor in the objectwise tensor presheaf, before
sheafification. -/
def tensorPure (M N : Modules R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (tensorPresheaf R M N).obj U :=
  m ⊗ₜ[R.obj.obj U] n

@[simp]
lemma tensorPure_zero_left (M N : Modules R) (U : Cᵒᵖ)
    (n : N.val.obj U) : tensorPure R M N U 0 n = 0 := by
  simp [tensorPure]
  rfl

@[simp]
lemma tensorPure_zero_right (M N : Modules R) (U : Cᵒᵖ)
    (m : M.val.obj U) : tensorPure R M N U m 0 = 0 := by
  simp [tensorPure]
  rfl

lemma tensorPure_add_left (M N : Modules R) (U : Cᵒᵖ)
    (m m' : M.val.obj U) (n : N.val.obj U) :
    tensorPure R M N U (m + m') n =
      tensorPure R M N U m n + tensorPure R M N U m' n := by
  simp only [tensorPure, TensorProduct.add_tmul]
  rfl

lemma tensorPure_add_right (M N : Modules R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n n' : N.val.obj U) :
    tensorPure R M N U m (n + n') =
      tensorPure R M N U m n + tensorPure R M N U m n' := by
  simp only [tensorPure, TensorProduct.tmul_add]
  rfl

lemma tensorPure_smul_left (M N : Modules R) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    tensorPure R M N U (a • m) n = a • tensorPure R M N U m n := by
  unfold tensorPure
  change ((show R.obj.obj U from a) •
      (show (directPresheaf R M).obj U from m)) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n) =
    (show R.obj.obj U from a) •
      ((show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n))
  rw [← TensorProduct.smul_tmul']

lemma tensorPure_smul_right (M N : Modules R) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    tensorPure R M N U m (a • n) = a • tensorPure R M N U m n := by
  unfold tensorPure
  change (show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
      ((show R.obj.obj U from a) •
        (show (directPresheaf R N).obj U from n)) =
    (show R.obj.obj U from a) •
      ((show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n))
  rw [TensorProduct.tmul_smul]

lemma map_tensorPure_add_left {P : PresheafOfModules (ringSheaf R).obj}
    (f : tensorPresheaf R M N ⟶ P) (U : Cᵒᵖ)
    (m m' : M.val.obj U) (n : N.val.obj U) :
    f.app U (tensorPure R M N U (m + m') n) =
      f.app U (tensorPure R M N U m n) +
        f.app U (tensorPure R M N U m' n) := by
  rw [tensorPure_add_left]
  exact map_add (f.app U).hom _ _

lemma map_tensorPure_add_right {P : PresheafOfModules (ringSheaf R).obj}
    (f : tensorPresheaf R M N ⟶ P) (U : Cᵒᵖ)
    (m : M.val.obj U) (n n' : N.val.obj U) :
    f.app U (tensorPure R M N U m (n + n')) =
      f.app U (tensorPure R M N U m n) +
        f.app U (tensorPure R M N U m n') := by
  rw [tensorPure_add_right]
  exact map_add (f.app U).hom _ _

lemma map_tensorPure_smul_left {P : PresheafOfModules (ringSheaf R).obj}
    (f : tensorPresheaf R M N ⟶ P) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    f.app U (tensorPure R M N U (a • m) n) =
      a • f.app U (tensorPure R M N U m n) := by
  rw [tensorPure_smul_left]
  exact map_smul (f.app U).hom a _

lemma map_tensorPure_smul_right {P : PresheafOfModules (ringSheaf R).obj}
    (f : tensorPresheaf R M N ⟶ P) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    f.app U (tensorPure R M N U m (a • n)) =
      a • f.app U (tensorPure R M N U m n) := by
  rw [tensorPure_smul_right]
  exact map_smul (f.app U).hom a _

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tensor product of sheaves of modules: sheafify the objectwise tensor
product. -/
noncomputable def tensorObj (M N : Modules R) : Modules R :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj
    (tensorPresheaf R M N)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private def unrestrictIdAppToFun
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (x : ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U) : P.obj U :=
  x

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma unrestrictIdAppToFun_add
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (x y : ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U) :
    unrestrictIdAppToFun R P U (x + y) =
      unrestrictIdAppToFun R P U x + unrestrictIdAppToFun R P U y :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma unrestrictIdAppToFun_smul
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U)
    (x : ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U) :
    unrestrictIdAppToFun R P U (a • x) =
      a • unrestrictIdAppToFun R P U x :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def unrestrictIdApp
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U ⟶ P.obj U :=
  ModuleCat.ofHom
    { toFun := unrestrictIdAppToFun R P U
      map_add' := unrestrictIdAppToFun_add R P U
      map_smul' := unrestrictIdAppToFun_smul R P U }

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma unrestrictIdApp_naturality
    (P : PresheafOfModules (ringSheaf R).obj) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).map f ≫
        (ModuleCat.restrictScalars ((ringSheaf R).obj.map f).hom).map
          (unrestrictIdApp R P V) =
      unrestrictIdApp R P U ≫ P.map f := by
  ext x
  rfl

/-- Remove restriction of scalars along the identity morphism of a ring
presheaf. -/
noncomputable def unrestrictId (P : PresheafOfModules (ringSheaf R).obj) :
    (PresheafOfModules.restrictScalars (𝟙 (ringSheaf R).obj)).obj P ⟶ P where
  app := unrestrictIdApp R P
  naturality := unrestrictIdApp_naturality R P

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private def restrictIdAppToFun
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (x : P.obj U) :
    ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U :=
  x

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma restrictIdAppToFun_add
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (x y : P.obj U) :
    restrictIdAppToFun R P U (x + y) =
      restrictIdAppToFun R P U x + restrictIdAppToFun R P U y :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma restrictIdAppToFun_smul
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (x : P.obj U) :
    restrictIdAppToFun R P U (a • x) =
      a • restrictIdAppToFun R P U x :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def restrictIdApp
    (P : PresheafOfModules (ringSheaf R).obj) (U : Cᵒᵖ) :
    P.obj U ⟶ ((PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P).obj U :=
  ModuleCat.ofHom
    { toFun := restrictIdAppToFun R P U
      map_add' := restrictIdAppToFun_add R P U
      map_smul' := restrictIdAppToFun_smul R P U }

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma restrictIdApp_naturality
    (P : PresheafOfModules (ringSheaf R).obj) {U V : Cᵒᵖ} (f : U ⟶ V) :
    P.map f ≫ (ModuleCat.restrictScalars
        ((ringSheaf R).obj.map f).hom).map (restrictIdApp R P V) =
      restrictIdApp R P U ≫
        ((PresheafOfModules.restrictScalars
          (𝟙 (ringSheaf R).obj)).obj P).map f := by
  ext x
  rfl

/-- Insert restriction of scalars along the identity. -/
noncomputable def restrictId (P : PresheafOfModules (ringSheaf R).obj) :
    P ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf R).obj)).obj P where
  app := restrictIdApp R P
  naturality := restrictIdApp_naturality R P

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction of scalars along an identity morphism is canonically
trivial. -/
private lemma unrestrictId_hom_inv_id
    (P : PresheafOfModules (ringSheaf R).obj) :
    unrestrictId R P ≫ restrictId R P = 𝟙 _ := by
  ext U x
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma unrestrictId_inv_hom_id
    (P : PresheafOfModules (ringSheaf R).obj) :
    restrictId R P ≫ unrestrictId R P = 𝟙 _ := by
  ext U x
  rfl

noncomputable def unrestrictIdIso (P : PresheafOfModules (ringSheaf R).obj) :
    (PresheafOfModules.restrictScalars (𝟙 (ringSheaf R).obj)).obj P ≅ P where
  hom := unrestrictId R P
  inv := restrictId R P
  hom_inv_id := unrestrictId_hom_inv_id R P
  inv_hom_id := unrestrictId_inv_hom_id R P

/-- The canonical map from the objectwise tensor presheaf into its
sheafification. -/
noncomputable def tensorUnit (M N : Modules R) :
    tensorPresheaf R M N ⟶ (tensorObj R M N).val :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf R).obj)).unit.app (tensorPresheaf R M N) ≫
    unrestrictId R (tensorObj R M N).val

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def postcompUnrestrictIdToFun
    (Q P : PresheafOfModules (ringSheaf R).obj)
    (f : Q ⟶ (PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P) : Q ⟶ P :=
  f ≫ (unrestrictIdIso R P).hom

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def postcompUnrestrictIdInvFun
    (Q P : PresheafOfModules (ringSheaf R).obj) (f : Q ⟶ P) :
    Q ⟶ (PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P :=
  f ≫ (unrestrictIdIso R P).inv

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma postcompUnrestrictId_left_inv
    (Q P : PresheafOfModules (ringSheaf R).obj)
    (f : Q ⟶ (PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P) :
    postcompUnrestrictIdInvFun R Q P
        (postcompUnrestrictIdToFun R Q P f) = f := by
  change f ≫ (unrestrictIdIso R P).hom ≫ (unrestrictIdIso R P).inv = f
  rw [Iso.hom_inv_id, Category.comp_id]

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma postcompUnrestrictId_right_inv
    (Q P : PresheafOfModules (ringSheaf R).obj) (f : Q ⟶ P) :
    postcompUnrestrictIdToFun R Q P
        (postcompUnrestrictIdInvFun R Q P f) = f := by
  change f ≫ (unrestrictIdIso R P).inv ≫ (unrestrictIdIso R P).hom = f
  rw [Iso.inv_hom_id, Category.comp_id]

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private noncomputable def postcompUnrestrictIdEquiv
    (Q P : PresheafOfModules (ringSheaf R).obj) :
    (Q ⟶ (PresheafOfModules.restrictScalars
      (𝟙 (ringSheaf R).obj)).obj P) ≃ (Q ⟶ P) where
  toFun := postcompUnrestrictIdToFun R Q P
  invFun := postcompUnrestrictIdInvFun R Q P
  left_inv := postcompUnrestrictId_left_inv R Q P
  right_inv := postcompUnrestrictId_right_inv R Q P

/-- Universal property of the tensor sheaf, expressed using the objectwise
tensor presheaf and the sheafification adjunction. -/
noncomputable def tensorHomEquiv (M N P : Modules R) :
    (tensorObj R M N ⟶ P) ≃
      (tensorPresheaf R M N ⟶
        (SheafOfModules.forget (ringSheaf R)).obj P) := by
  let Pv := (SheafOfModules.forget (ringSheaf R)).obj P
  let e := (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (ringSheaf R).obj) :
        (tensorObj R M N ⟶ P) ≃
          (tensorPresheaf R M N ⟶
            (PresheafOfModules.restrictScalars
              (𝟙 (ringSheaf R).obj)).obj Pv))
  exact e.trans (postcompUnrestrictIdEquiv R (tensorPresheaf R M N) Pv)

/-- Lift a morphism out of the objectwise tensor presheaf to a morphism out of
the tensor sheaf. -/
noncomputable def tensorLift {M N P : Modules R}
    (f : tensorPresheaf R M N ⟶ P.val) : tensorObj R M N ⟶ P :=
  (tensorHomEquiv R M N P).symm f

@[simp]
lemma tensorHomEquiv_tensorLift {M N P : Modules R}
    (f : tensorPresheaf R M N ⟶ P.val) :
    tensorHomEquiv R M N P (tensorLift R f) = f :=
  (tensorHomEquiv R M N P).apply_symm_apply f

/-- The image of a pure tensor in the tensor sheaf. -/
noncomputable def tmul (M N : Modules R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) : (tensorObj R M N).val.obj U :=
  (tensorUnit R M N).app U (tensorPure R M N U m n)

@[simp]
lemma zero_tmul (M N : Modules R) (U : Cᵒᵖ) (n : N.val.obj U) :
    tmul R M N U 0 n = 0 := by
  unfold tmul
  rw [tensorPure_zero_left]
  exact map_zero ((tensorUnit R M N).app U).hom

@[simp]
lemma tmul_zero (M N : Modules R) (U : Cᵒᵖ) (m : M.val.obj U) :
    tmul R M N U m 0 = 0 := by
  unfold tmul
  rw [tensorPure_zero_right]
  exact map_zero ((tensorUnit R M N).app U).hom

lemma add_tmul (M N : Modules R) (U : Cᵒᵖ)
    (m m' : M.val.obj U) (n : N.val.obj U) :
    tmul R M N U (m + m') n = tmul R M N U m n + tmul R M N U m' n := by
  unfold tmul
  rw [tensorPure_add_left]
  exact map_add ((tensorUnit R M N).app U).hom _ _

lemma tmul_add (M N : Modules R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n n' : N.val.obj U) :
    tmul R M N U m (n + n') = tmul R M N U m n + tmul R M N U m n' := by
  unfold tmul
  rw [tensorPure_add_right]
  exact map_add ((tensorUnit R M N).app U).hom _ _

lemma smul_tmul (M N : Modules R) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    tmul R M N U (a • m) n = a • tmul R M N U m n := by
  unfold tmul tensorPure
  change ((tensorUnit R M N).app U).hom
      (((show R.obj.obj U from a) •
          (show (directPresheaf R M).obj U from m)) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n)) =
    a • ((tensorUnit R M N).app U).hom
      ((show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n))
  rw [← TensorProduct.smul_tmul']
  exact map_smul ((tensorUnit R M N).app U).hom a _

lemma tmul_smul (M N : Modules R) (U : Cᵒᵖ)
    (a : (ringSheaf R).obj.obj U) (m : M.val.obj U) (n : N.val.obj U) :
    tmul R M N U m (a • n) = a • tmul R M N U m n := by
  unfold tmul tensorPure
  change ((tensorUnit R M N).app U).hom
      ((show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
        ((show R.obj.obj U from a) •
          (show (directPresheaf R N).obj U from n))) =
    a • ((tensorUnit R M N).app U).hom
      ((show (directPresheaf R M).obj U from m) ⊗ₜ[R.obj.obj U]
        (show (directPresheaf R N).obj U from n))
  rw [TensorProduct.tmul_smul]
  exact map_smul ((tensorUnit R M N).app U).hom a _

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Objectwise restriction sends a pure tensor to the tensor of the two
restricted sections. -/
lemma tensorPure_map (M N : Modules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (tensorPresheaf R M N).map f (tensorPure R M N U m n) =
      tensorPure R M N V (M.val.map f m) (N.val.map f n) := by
  rfl

/-- Pure tensors commute with restriction maps. -/
lemma tmul_map (M N : Modules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (show (tensorObj R M N).val.obj V from
      (tensorObj R M N).val.map f (tmul R M N U m n)) =
      tmul R M N V (M.val.map f m) (N.val.map f n) := by
  let t : (tensorPresheaf R M N).obj U := tensorPure R M N U m n
  have h := PresheafOfModules.naturality_apply (tensorUnit R M N) f t
  change (tensorObj R M N).val.map f
      ((tensorUnit R M N).app U (tensorPure R M N U m n)) =
    (tensorUnit R M N).app V
      (tensorPure R M N V (M.val.map f m) (N.val.map f n))
  calc
    _ = (tensorUnit R M N).app V ((tensorPresheaf R M N).map f t) := h.symm
    _ = _ := congrArg (fun x ↦ (tensorUnit R M N).app V x)
      (tensorPure_map R M N f m n)

/-- The objectwise tensor morphism, expressed through the visibly composed
commutative-ring presheaf. -/
noncomputable def tensorPresheafHom {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorPresheaf R M N ⟶ tensorPresheaf R M' N' := by
  change directPresheaf R M ⊗ directPresheaf R N ⟶
    directPresheaf R M' ⊗ directPresheaf R N'
  exact directHom R f ⊗ₘ directHom R g

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma tensorPresheafHom_tensorPure {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (tensorPresheafHom R f g).app U (tensorPure R M N U m n) =
      tensorPure R M' N' U (f.val.app U m) (g.val.app U n) := by
  rfl

/-- Tensor product of two morphisms of module sheaves. -/
noncomputable def tensorHom {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj R M N ⟶ tensorObj R M' N' :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map
    (tensorPresheafHom R f g)

/-- Tensor products of morphisms act on pure tensors in the expected way. -/
lemma tensorHom_tmul {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (tensorHom R f g).val.app U (tmul R M N U m n) =
      tmul R M' N' U (f.val.app U m) (g.val.app U n) := by
  let h : tensorPresheaf R M N ⟶ tensorPresheaf R M' N' :=
    tensorPresheafHom R f g
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf R).obj)).unit.naturality h
  have hnU := congrArg (fun q ↦ q.app U) hn
  have hnx := congrArg (fun q ↦ q.hom (tensorPure R M N U m n)) hnU
  have hu := congrArg
    (fun x ↦ (unrestrictId R (tensorObj R M' N').val).app U x) hnx.symm
  change (tensorHom R f g).val.app U
      ((tensorUnit R M N).app U (tensorPure R M N U m n)) =
    (tensorUnit R M' N').app U
      ((tensorPresheafHom R f g).app U (tensorPure R M N U m n)) at hu
  calc
    _ = (tensorUnit R M' N').app U
        ((tensorPresheafHom R f g).app U (tensorPure R M N U m n)) := hu
    _ = _ := congrArg (fun x ↦ (tensorUnit R M' N').app U x)
      (tensorPresheafHom_tensorPure R f g U m n)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
@[simp]
lemma directHom_id (M : Modules R) :
    directHom R (𝟙 M) = 𝟙 (directPresheaf R M) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
@[simp]
lemma directHom_comp {M N P : Modules R} (f : M ⟶ N) (g : N ⟶ P) :
    directHom R (f ≫ g) = directHom R f ≫ directHom R g := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
@[simp]
lemma tensorPresheafHom_id (M N : Modules R) :
    tensorPresheafHom R (𝟙 M) (𝟙 N) = 𝟙 (tensorPresheaf R M N) := by
  change (directHom R (𝟙 M) ⊗ₘ directHom R (𝟙 N)) =
    𝟙 (directPresheaf R M ⊗ directPresheaf R N)
  simp

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
@[simp]
lemma tensorPresheafHom_comp {M M' M'' N N' N'' : Modules R}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    tensorPresheafHom R (f ≫ f') (g ≫ g') =
      tensorPresheafHom R f g ≫ tensorPresheafHom R f' g' := by
  change (directHom R (f ≫ f') ⊗ₘ directHom R (g ≫ g')) =
    (directHom R f ⊗ₘ directHom R g) ≫
      (directHom R f' ⊗ₘ directHom R g')
  rw [directHom_comp, directHom_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]

@[simp]
lemma tensorHom_id (M N : Modules R) :
    tensorHom R (𝟙 M) (𝟙 N) = 𝟙 (tensorObj R M N) := by
  unfold tensorHom
  rw [tensorPresheafHom_id]
  let F := PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)
  change F.map (𝟙 (tensorPresheaf R M N)) =
    (𝟙 (F.obj (tensorPresheaf R M N)) :
      F.obj (tensorPresheaf R M N) ⟶ F.obj (tensorPresheaf R M N))
  exact F.map_id _

@[simp]
lemma tensorHom_comp {M M' M'' N N' N'' : Modules R}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    tensorHom R (f ≫ f') (g ≫ g') =
      tensorHom R f g ≫ tensorHom R f' g' := by
  let F := PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)
  change F.map (tensorPresheafHom R (f ≫ f') (g ≫ g')) =
    F.map (tensorPresheafHom R f g) ≫ F.map (tensorPresheafHom R f' g')
  rw [tensorPresheafHom_comp, F.map_comp]

private noncomputable def tensorBifunctorObj
    (MN : Modules R × Modules R) : Modules R :=
  tensorObj R MN.1 MN.2

private noncomputable def tensorBifunctorMap
    {MN MN' : Modules R × Modules R} (f : MN ⟶ MN') :
    tensorBifunctorObj R MN ⟶ tensorBifunctorObj R MN' :=
  tensorHom R f.1 f.2

/-- The tensor product as a bifunctor on sheaves of modules. -/
noncomputable def tensorBifunctor : Modules R × Modules R ⥤ Modules R where
  obj := tensorBifunctorObj R
  map := tensorBifunctorMap R
  map_id MN := tensorHom_id R MN.1 MN.2
  map_comp f g := tensorHom_comp R f.1 g.1 f.2 g.2

/-- The tensor bifunctor acts on a pair of morphisms by the previously
constructed tensor morphism. -/
@[simp]
lemma tensorBifunctor_map {MN MN' : Modules R × Modules R}
    (f : MN ⟶ MN') :
    (tensorBifunctor R).map f = tensorHom R f.1 f.2 :=
  rfl

end

end CommRingSheaf

end

end LSZ
