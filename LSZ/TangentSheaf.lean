import LSZ.VectorFields
import LSZ.SheafTensor

/-!
# The tangent sheaf and the Higgs tensor sheaf

The relative vector fields constructed in `LSZ.VectorFields` form a
presheaf of modules over the structure sheaf.  We sheafify that presheaf to
obtain an actual object of `X.Modules`.  The tensor product used below is
the tensor product over the sheaf of rings from `LSZ.SheafTensor`; it is not
a construction specific to schemes.
-/

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- The scalar action carried by the bundled `ModuleCat` section agrees
with the usual scheme-section scalar action. -/
lemma bundled_smul_eq_smul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (m : Γ(M, U)) :
    (((M.val.obj (.op U)).smul
      (show X.scheme.ringCatSheaf.obj.obj (.op U) from a)).hom m) =
      a • m := by
  rfl

namespace VectorField

/-- Scalar multiplication, named so it can be used while assembling the
presheaf-of-modules structure. -/
def smulAt (U : X.scheme.Opens) (a : Γ(X.scheme, U))
    (D : X.VectorField U) : X.VectorField U :=
  a • D

end VectorField

/-- The additive presheaf of canonical relative vector fields. -/
def vectorFieldAbPresheaf : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (X.VectorField U.unop)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun D ↦ D.restrict (leOfHom f.unop)
      map_zero' := by ext W hW a; rfl
      map_add' := by intro D E; ext W hW a; rfl }
  map_id U := by
    ext D W hW a
    rfl
  map_comp f g := by
    ext D W hW a
    rfl

lemma vectorFieldAbPresheaf_map_smul {U V : X.scheme.Opensᵒᵖ}
    (f : U ⟶ V) (a : Γ(X.scheme, U.unop))
    (D : X.VectorField U.unop) :
    (vectorFieldAbPresheaf X).map f (a • D) =
      VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
        (D.restrict (leOfHom f.unop)) := by
  change (a • D).restrict (leOfHom f.unop) =
    VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
      (D.restrict (leOfHom f.unop))
  ext W hW b
  change X.scheme.presheaf.map
      (homOfLE (hW.trans (leOfHom f.unop))).op a *
        D.deriv W (hW.trans (leOfHom f.unop)) b =
    X.scheme.presheaf.map (homOfLE hW).op
        (X.scheme.presheaf.map f a) *
      D.deriv W (hW.trans (leOfHom f.unop)) b
  congr 1
  rw [← CommRingCat.comp_apply, ← X.scheme.presheaf.map_comp]
  rfl

/-- Canonical relative vector fields as a presheaf of modules over
`ᵊa_X`. -/
def vectorFieldPresheaf : X.scheme.PresheafOfModules := by
  letI (U : X.scheme.Opensᵒᵖ) :
      Module (X.scheme.ringCatSheaf.obj.obj U)
        ((vectorFieldAbPresheaf X).obj U) := by
    change Module Γ(X.scheme, U.unop) (X.VectorField U.unop)
    infer_instance
  apply PresheafOfModules.ofPresheaf (vectorFieldAbPresheaf X)
  intro U V f a D
  change (a • D).restrict (leOfHom f.unop) =
    VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
      (D.restrict (leOfHom f.unop))
  exact vectorFieldAbPresheaf_map_smul X f a D

/-- The tangent sheaf obtained by sheafifying the canonical presheaf of
relative vector fields. -/
def tangent : X.scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.scheme.ringCatSheaf.obj)).obj
    (vectorFieldPresheaf X)

/-- The unit from canonical vector fields into the tangent sheaf. -/
def tangentUnit : vectorFieldPresheaf X ⟶ (tangent X).val :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.scheme.ringCatSheaf.obj)).unit.app (vectorFieldPresheaf X) ≫
    CommRingSheaf.unrestrictId X.scheme.sheaf (tangent X).val

/-- Regard an explicit canonical vector field as a section of the vector
field presheaf. -/
def vectorFieldAsPresheafSection (U : X.scheme.Opens) (D : X.VectorField U) :
    (vectorFieldPresheaf X).obj (.op U) := by
  unfold vectorFieldPresheaf
  exact D

@[simp]
lemma vectorFieldAsPresheafSection_map {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) :
    (vectorFieldPresheaf X).map (homOfLE hVU).op
        (vectorFieldAsPresheafSection X U D) =
      vectorFieldAsPresheafSection X V (D.restrict hVU) := by
  change D.restrict hVU = D.restrict hVU
  rfl

lemma vectorFieldAsPresheafSection_smul (U : X.scheme.Opens)
    (a : X.scheme.ringCatSheaf.obj.obj (.op U)) (D : X.VectorField U) :
    vectorFieldAsPresheafSection X U ((show Γ(X.scheme, U) from a) • D) =
      a • vectorFieldAsPresheafSection X U D := by
  rfl

/-- An explicit canonical vector field gives a section of the tangent
sheaf. -/
def tangentSection (U : X.scheme.Opens) (D : X.VectorField U) :
    Γ(tangent X, U) :=
  (tangentUnit X).app (.op U) (vectorFieldAsPresheafSection X U D)

@[simp]
lemma tangentSection_zero (U : X.scheme.Opens) :
    tangentSection X U 0 = 0 := by
  exact map_zero ((tangentUnit X).app (.op U)).hom

lemma tangentSection_add (U : X.scheme.Opens) (D E : X.VectorField U) :
    tangentSection X U (D + E) =
      tangentSection X U D + tangentSection X U E := by
  exact map_add ((tangentUnit X).app (.op U)).hom D E

lemma tangentSection_smul (U : X.scheme.Opens)
    (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    tangentSection X U (a • D) = a • tangentSection X U D := by
  let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
  change (tangentUnit X).app (.op U)
      (vectorFieldAsPresheafSection X U (a • D)) =
    a • tangentSection X U D
  rw [vectorFieldAsPresheafSection_smul X U a' D]
  exact (map_smul ((tangentUnit X).app (.op U)).hom a'
    (vectorFieldAsPresheafSection X U D)).trans
      (bundled_smul_eq_smul X (tangent X) U a (tangentSection X U D))

@[simp]
lemma tangentSection_restrict {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) :
    (tangent X).val.map (homOfLE hVU).op (tangentSection X U D) =
      tangentSection X V (D.restrict hVU) := by
  rw [tangentSection, tangentSection,
    ← vectorFieldAsPresheafSection_map X hVU D]
  exact (PresheafOfModules.naturality_apply (tangentUnit X)
    (homOfLE hVU).op (vectorFieldAsPresheafSection X U D)).symm

/-- `ᵊf_X ⊗_{ᵊa_X} M`, formed using the tensor product of module
sheaves on the underlying ringed space. -/
def higgsTensor (M : X.scheme.Modules) : X.scheme.Modules :=
  CommRingSheaf.tensorObj X.scheme.sheaf (tangent X) M

/-- The pure tensor `D ⊗ m` in the Higgs tensor sheaf. -/
def higgsTmul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(M, U)) : Γ(higgsTensor X M, U) :=
  CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D) m

@[simp]
lemma higgsTmul_zero_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (m : Γ(M, U)) :
    higgsTmul X M U 0 m = 0 := by
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U 0) m = 0
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U) 0 m :=
      congrArg (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf
        (tangent X) M (.op U) t m) (tangentSection_zero X U)
    _ = 0 := CommRingSheaf.zero_tmul X.scheme.sheaf
      (tangent X) M (.op U) m

lemma higgsTmul_add_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D E : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U (D + E) m =
      higgsTmul X M U D m + higgsTmul X M U E m := by
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
      (tangentSection X U (D + E)) m =
    CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U D) m +
      CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U E) m
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U D + tangentSection X U E) m :=
      congrArg (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf
        (tangent X) M (.op U) t m) (tangentSection_add X U D E)
    _ = _ := CommRingSheaf.add_tmul X.scheme.sheaf
      (tangent X) M (.op U) (tangentSection X U D)
        (tangentSection X U E) m

lemma higgsTmul_smul_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (D : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U (a • D) m = a • higgsTmul X M U D m := by
  let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
  unfold higgsTmul
  rw [tangentSection_smul X U a D]
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        ((((tangent X).val.obj (.op U)).smul a').hom
          (tangentSection X U D)) m =
      (((higgsTensor X M).val.obj (.op U)).smul a').hom
        (CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
          (tangentSection X U D) m)
  exact CommRingSheaf.smul_tmul X.scheme.sheaf
    (tangent X) M (.op U) a' (tangentSection X U D) m

@[simp]
lemma higgsTmul_zero_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) :
    higgsTmul X M U D 0 = 0 := by
  exact CommRingSheaf.tmul_zero X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D)

lemma higgsTmul_add_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m n : Γ(M, U)) :
    higgsTmul X M U D (m + n) =
      higgsTmul X M U D m + higgsTmul X M U D n := by
  exact CommRingSheaf.tmul_add X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D) m n

lemma higgsTmul_smul_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (D : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U D (a • m) = a • higgsTmul X M U D m := by
  exact CommRingSheaf.tmul_smul X.scheme.sheaf (tangent X) M (.op U) a
    (tangentSection X U D) m

@[simp]
lemma higgsTmul_restrict (M : X.scheme.Modules) {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) (m : Γ(M, U)) :
    (higgsTensor X M).presheaf.map (homOfLE hVU).op
        (higgsTmul X M U D m) =
      higgsTmul X M V (D.restrict hVU)
        (M.presheaf.map (homOfLE hVU).op m) := by
  change (higgsTensor X M).val.map (homOfLE hVU).op
      (higgsTmul X M U D m) =
    higgsTmul X M V (D.restrict hVU)
      (M.val.map (homOfLE hVU).op m)
  have h := CommRingSheaf.tmul_map X.scheme.sheaf (tangent X) M
    (homOfLE hVU).op (tangentSection X U D) m
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op V)
        ((tangent X).val.map (homOfLE hVU).op (tangentSection X U D))
        (M.val.map (homOfLE hVU).op m) := h
    _ = _ := congrArg
      (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op V)
        t (M.val.map (homOfLE hVU).op m))
      (tangentSection_restrict X hVU D)

/-- Functoriality of the Higgs tensor sheaf in its coefficient module. -/
def higgsTensorMap {M N : X.scheme.Modules} (f : M ⟶ N) :
    higgsTensor X M ⟶ higgsTensor X N :=
  CommRingSheaf.tensorHom X.scheme.sheaf (𝟙 (tangent X)) f

@[simp]
lemma higgsTensorMap_tmul {M N : X.scheme.Modules} (f : M ⟶ N)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M, U)) :
    (higgsTensorMap X f).app U (higgsTmul X M U D m) =
      higgsTmul X N U D (f.app U m) := by
  have h := CommRingSheaf.tensorHom_tmul X.scheme.sheaf
    (𝟙 (tangent X)) f (.op U) (tangentSection X U D) m
  exact h

@[simp]
lemma higgsTensorMap_id (M : X.scheme.Modules) :
    higgsTensorMap X (𝟙 M) = 𝟙 (higgsTensor X M) := by
  exact CommRingSheaf.tensorHom_id X.scheme.sheaf (tangent X) M

@[simp]
lemma higgsTensorMap_comp {M N P : X.scheme.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    higgsTensorMap X (f ≫ g) =
      higgsTensorMap X f ≫ higgsTensorMap X g := by
  exact CommRingSheaf.tensorHom_comp X.scheme.sheaf
    (𝟙 (tangent X)) (𝟙 (tangent X)) f g

end

end LSZ.SmoothScheme
