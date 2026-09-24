import LSZ.ConnectionTensorSheafification
import LSZ.DirectFrobeniusPullback
import LSZ.GeometricObjects
import Mathlib.Topology.Sheaves.Stalks

/-!
# The canonical derivative on the direct Frobenius pullback presheaf

The direct presentation of Frobenius pullback has sections
`O_X(U) \otimes_{F,O_X(U)} M(U)`.  This file equips those sections with the
canonical derivative

`nabla_D (a \otimes m) = D(a) \otimes m`

and proves that it commutes with restriction.  The construction is the
objectwise `ModuleCat.extendScalars` construction from
`StandardCanonicalConnection`; no second tensor-product model is introduced.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry TensorProduct ModuleCat.Algebra ChangeOfRings

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {p : ℕ} {k : Type u}
variable [Field k] [CharP k p] [Fact p.Prime]

/-- The canonical derivative in one vector-field direction on the direct
Frobenius-pullback presheaf. -/
noncomputable abbrev directCanonicalNablaAdd
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop) :
    (directFrobeniusPullbackPresheaf (p := p) X M).obj U →+
      (directFrobeniusPullbackPresheaf (p := p) X M).obj U :=
  StandardFrobeniusPullback.canonicalNablaAdd k
    Γ(X.scheme, U.unop) Γ(M, U.unop) p D.act

@[simp]
lemma directCanonicalNablaAdd_tmul
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop)
    (a : Γ(X.scheme, U.unop)) (m : Γ(M, U.unop)) :
    directCanonicalNablaAdd (p := p) X M U D
        (directFrobeniusPullbackTmul (p := p) X M U a m) =
      directFrobeniusPullbackTmul (p := p) X M U (D.act a) m := by
  rw [directFrobeniusPullbackTmul_eq_standard,
    directFrobeniusPullbackTmul_eq_standard]
  exact StandardFrobeniusPullback.canonicalNablaAdd_tmul
    k Γ(X.scheme, U.unop) Γ(M, U.unop) p D.act a m

set_option backward.isDefEq.respectTransparency false in
lemma directCanonicalNablaAdd_add_vectorField
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D E : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalNablaAdd (p := p) X M U (D + E) x =
      directCanonicalNablaAdd (p := p) X M U D x +
        directCanonicalNablaAdd (p := p) X M U E x := by
  have h := congrArg
    (fun T : Module.End k
      (StandardFrobeniusPullback.obj k
        Γ(X.scheme, U.unop) Γ(M, U.unop) p) ↦ T x)
    (map_add (StandardFrobeniusPullback.canonicalNabla
      k Γ(X.scheme, U.unop) Γ(M, U.unop) p) D.act E.act)
  exact h

set_option backward.isDefEq.respectTransparency false in
lemma directCanonicalNablaAdd_smul_vectorField
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (a : Γ(X.scheme, U.unop))
    (D : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalNablaAdd (p := p) X M U (a • D) x =
      a • directCanonicalNablaAdd (p := p) X M U D x := by
  have hact : (a • D).act = a • D.act := by
    ext b
    change (a • D).deriv U.unop le_rfl b =
      (a • D.deriv U.unop le_rfl) b
    rw [VectorField.smul_deriv]
    let j : U ⟶ U := (homOfLE le_rfl).op
    change X.scheme.presheaf.map j a * D.act b =
      a * D.act b
    congr 1
    have hi : j = 𝟙 U := Subsingleton.elim _ _
    rw [hi, X.scheme.presheaf.map_id]
    rfl
  have h := congrArg
    (fun T : Module.End k
      (StandardFrobeniusPullback.obj k
        Γ(X.scheme, U.unop) Γ(M, U.unop) p) ↦ T x)
    (map_smul (StandardFrobeniusPullback.canonicalNabla
      k Γ(X.scheme, U.unop) Γ(M, U.unop) p) a D.act)
  change StandardFrobeniusPullback.canonicalNablaAdd k
      Γ(X.scheme, U.unop) Γ(M, U.unop) p (a • D).act x = _
  rw [hact]
  exact h

/-- The canonical derivative in one direction, bundled as a
`Z`-linear endomorphism. -/
noncomputable def directCanonicalNablaEnd
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop) :
    Module.End ℤ
      ((directFrobeniusPullbackPresheaf (p := p) X M).obj U) where
  toFun := directCanonicalNablaAdd (p := p) X M U D
  map_add' := map_add _
  map_smul' n x := map_zsmul
    (directCanonicalNablaAdd (p := p) X M U D) n x

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derivative, linear in the vector-field direction. -/
noncomputable def directCanonicalNabla
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) :
    X.VectorField U.unop →ₗ[Γ(X.scheme, U.unop)]
      Module.End ℤ
        ((directFrobeniusPullbackPresheaf (p := p) X M).obj U) where
  toFun := directCanonicalNablaEnd (p := p) X M U
  map_add' D E := by
    ext x
    exact directCanonicalNablaAdd_add_vectorField
      (p := p) X M U D E x
  map_smul' a D := by
    ext x
    exact directCanonicalNablaAdd_smul_vectorField
      (p := p) X M U a D x

@[simp]
lemma directCanonicalNabla_apply
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalNabla (p := p) X M U D x =
      directCanonicalNablaAdd (p := p) X M U D x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derivative is compatible with restriction of the vector
field and of the Frobenius-pullback section. -/
lemma directCanonicalNablaAdd_naturality
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    {U V : X.scheme.Opensᵒᵖ} (i : U ⟶ V)
    (D : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    (directFrobeniusPullbackPresheaf (p := p) X M).map i
        (directCanonicalNablaAdd (p := p) X M U D x) =
      directCanonicalNablaAdd (p := p) X M V (D.restrict i.unop.le)
        ((directFrobeniusPullbackPresheaf (p := p) X M).map i x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      let P := directFrobeniusPullbackPresheaf (p := p) X M
      let CU := directCanonicalNablaAdd (p := p) X M U D
      let CV := directCanonicalNablaAdd (p := p) X M V
        (D.restrict i.unop.le)
      have hCU : CU 0 = 0 := CU.map_zero
      have hP : P.map i (0 : P.obj U) = (0 : P.obj V) :=
        (P.map i).hom.map_zero
      have hCV : CV 0 = 0 := CV.map_zero
      exact (congrArg (fun z ↦ P.map i z) hCU).trans
        (hP.trans (hCV.symm.trans (congrArg CV hP.symm)))
  | tmul a m =>
      let a' : Γ(X.scheme, U.unop) := a
      let m' : Γ(M, U.unop) := m
      change (directFrobeniusPullbackPresheaf (p := p) X M).map i
          (directCanonicalNablaAdd (p := p) X M U D
            (StandardFrobeniusPullback.tmul k
              Γ(X.scheme, U.unop) Γ(M, U.unop) p a' m')) =
        directCanonicalNablaAdd (p := p) X M V (D.restrict i.unop.le)
          ((directFrobeniusPullbackPresheaf (p := p) X M).map i
            (StandardFrobeniusPullback.tmul k
              Γ(X.scheme, U.unop) Γ(M, U.unop) p a' m'))
      let P := directFrobeniusPullbackPresheaf (p := p) X M
      let CU := directCanonicalNablaAdd (p := p) X M U D
      let CV := directCanonicalNablaAdd (p := p) X M V
        (D.restrict i.unop.le)
      let tU := directFrobeniusPullbackTmul (p := p) X M U a' m'
      let tV := directFrobeniusPullbackTmul (p := p) X M V
        (X.scheme.presheaf.map i a') (M.val.map i m')
      let dtV := directFrobeniusPullbackTmul (p := p) X M V
        ((D.restrict i.unop.le).act (X.scheme.presheaf.map i a'))
        (M.val.map i m')
      have hstd : StandardFrobeniusPullback.tmul k
          Γ(X.scheme, U.unop) Γ(M, U.unop) p a' m' = tU :=
        (directFrobeniusPullbackTmul_eq_standard
          (p := p) X M U a' m').symm
      have hcanU : CU tU =
          directFrobeniusPullbackTmul (p := p) X M U (D.act a') m' :=
        directCanonicalNablaAdd_tmul (p := p) X M U D a' m'
      have hmapD : P.map i
          (directFrobeniusPullbackTmul (p := p) X M U (D.act a') m') =
          directFrobeniusPullbackTmul (p := p) X M V
            (X.scheme.presheaf.map i (D.act a')) (M.val.map i m') :=
        directFrobeniusPullbackTmul_map
          (p := p) X M i (D.act a') m'
      have hD : X.scheme.presheaf.map i (D.act a') =
          (D.restrict i.unop.le).act (X.scheme.presheaf.map i a') :=
        D.compatible le_rfl i.unop.le a'
      have hreplace : directFrobeniusPullbackTmul (p := p) X M V
            (X.scheme.presheaf.map i (D.act a')) (M.val.map i m') = dtV :=
        congrArg (fun b ↦ directFrobeniusPullbackTmul
          (p := p) X M V b (M.val.map i m')) hD
      have hcanV : dtV = CV tV :=
        (directCanonicalNablaAdd_tmul (p := p) X M V
          (D.restrict i.unop.le) (X.scheme.presheaf.map i a')
            (M.val.map i m')).symm
      have hmap : P.map i tU = tV :=
        directFrobeniusPullbackTmul_map (p := p) X M i a' m'
      exact (congrArg (fun z ↦ P.map i (CU z)) hstd).trans
        ((congrArg (fun z ↦ P.map i z) hcanU).trans
          (hmapD.trans (hreplace.trans
            (hcanV.trans ((congrArg CV hmap.symm).trans
              (congrArg (fun z ↦ CV (P.map i z)) hstd.symm))))))
  | add x y hx hy =>
      let P := directFrobeniusPullbackPresheaf (p := p) X M
      let CU := directCanonicalNablaAdd (p := p) X M U D
      let CV := directCanonicalNablaAdd (p := p) X M V
        (D.restrict i.unop.le)
      have hCU : CU (x + y) = CU x + CU y := CU.map_add x y
      have hP₁ : P.map i (CU x + CU y) =
          P.map i (CU x) + P.map i (CU y) :=
        (P.map i).hom.map_add _ _
      have hP₂ : P.map i (x + y) = P.map i x + P.map i y :=
        (P.map i).hom.map_add _ _
      have hCV : CV (P.map i x + P.map i y) =
          CV (P.map i x) + CV (P.map i y) := CV.map_add _ _
      exact (congrArg (fun z ↦ P.map i z) hCU).trans
        (hP₁.trans ((congrArg₂ (fun a b ↦ a + b) hx hy).trans
          (hCV.symm.trans (congrArg CV hP₂.symm))))

set_option backward.isDefEq.respectTransparency false in
lemma directCanonicalNablaAdd_leibniz
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop)
    (a : Γ(X.scheme, U.unop))
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalNablaAdd (p := p) X M U D (a • x) =
      a • directCanonicalNablaAdd (p := p) X M U D x + D.act a • x :=
  StandardFrobeniusPullback.canonicalNablaAdd_leibniz
    k Γ(X.scheme, U.unop) Γ(M, U.unop) p D.act a x

set_option backward.isDefEq.respectTransparency false in
lemma directCanonicalNablaAdd_flat
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D E : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalNablaAdd (p := p) X M U ⁅D, E⁆ x =
      directCanonicalNablaAdd (p := p) X M U D
          (directCanonicalNablaAdd (p := p) X M U E x) -
        directCanonicalNablaAdd (p := p) X M U E
          (directCanonicalNablaAdd (p := p) X M U D x) :=
  StandardFrobeniusPullback.canonicalNabla_flat
    k Γ(X.scheme, U.unop) Γ(M, U.unop) p D.act E.act x

private noncomputable def directCanonicalActionApp
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) :
    (connectionTensorModulePresheafOf X
      (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).obj U ⟶
    (asIntegerModulePresheaf X
      (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun D x ↦ directCanonicalNablaAdd (p := p) X M U
      (show X.VectorField U.unop from D) x)
    (by
      intro D E x
      exact directCanonicalNablaAdd_add_vectorField
        (p := p) X M U D E x)
    (by
      intro n D x
      change directCanonicalNablaAdd (p := p) X M U (n.down • D) x =
        n.down • directCanonicalNablaAdd (p := p) X M U D x
      have h := congrArg
        (fun T : Module.End ℤ
          ((directFrobeniusPullbackPresheaf (p := p) X M).obj U) ↦ T x)
        (map_zsmul (directCanonicalNabla (p := p) X M U) n.down D)
      exact h)
    (by
      intro D x y
      exact map_add (directCanonicalNablaAdd (p := p) X M U D) x y)
    (by
      intro n D x
      change directCanonicalNablaAdd (p := p) X M U D (n.down • x) =
        n.down • directCanonicalNablaAdd (p := p) X M U D x
      exact map_zsmul
        (directCanonicalNablaAdd (p := p) X M U D) n.down x)

@[simp]
private lemma directCanonicalActionApp_tmul
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    directCanonicalActionApp (p := p) X M U
        (connectionTensorPureOf X
          (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
          U.unop D x) =
      directCanonicalNablaAdd (p := p) X M U D x := by
  rfl

/-- The joint canonical action of vector fields on the direct Frobenius
pullback, as a morphism of module presheaves over the lifted integers. -/
noncomputable def directCanonicalAction
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    connectionTensorModulePresheafOf X
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf ⟶
      asIntegerModulePresheaf X
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf where
  app U := directCanonicalActionApp (p := p) X M U
  naturality := by
    intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro D x
    change directCanonicalNablaAdd (p := p) X M V
        ((show X.VectorField U.unop from D).restrict i.unop.le)
        ((directFrobeniusPullbackPresheaf (p := p) X M).map i x) =
      (directFrobeniusPullbackPresheaf (p := p) X M).map i
        (directCanonicalNablaAdd (p := p) X M U D x)
    exact (directCanonicalNablaAdd_naturality
      (p := p) X M i D x).symm

@[simp]
lemma directCanonicalAction_tmul
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (D : X.VectorField U.unop)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    (directCanonicalAction (p := p) X M).app U
        (connectionTensorPureOf X
          (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
          U.unop D x) =
      directCanonicalNablaAdd (p := p) X M U D x := by
  rfl

/-- The underlying additive-presheaf morphism of the joint canonical
action. -/
noncomputable def directCanonicalActionPresheaf
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    connectionTensorPresheafOf X
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf ⟶
      (directFrobeniusPullbackPresheaf (p := p) X M).presheaf :=
  (PresheafOfModules.toPresheaf
    (liftedIntegerPresheaf X ⋙ forget₂ CommRingCat RingCat)).map
      (directCanonicalAction (p := p) X M)

/-- Sheafification of the canonical action on the direct presentation. -/
noncomputable def sheafifiedDirectCanonicalAction
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    connectionTensorSheafOf X
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf ⟶
      (presheafToSheaf (Opens.grothendieckTopology X.scheme)
        AddCommGrpCat.{u}).obj
          (directFrobeniusPullbackPresheaf (p := p) X M).presheaf :=
  (presheafToSheaf (Opens.grothendieckTopology X.scheme)
    AddCommGrpCat.{u}).map (directCanonicalActionPresheaf (p := p) X M)

/-- The canonical connection map on the actual sheafified direct
Frobenius pullback.  The inverse comparison is forced by the fact that the
connection tensor is formed after the coefficient presheaf has been
sheafified. -/
noncomputable def directCanonicalConnectionHom
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    connectionTensor X ((directFrobeniusPullbackFunctor (p := p) X).obj M) ⟶
      (SheafOfModules.toSheaf X.scheme.ringCatSheaf).obj
        ((directFrobeniusPullbackFunctor (p := p) X).obj M) :=
  (connectionTensorSheafificationIso X
      (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).inv ≫
    sheafifiedDirectCanonicalAction (p := p) X M

/-- On sections coming from the objectwise extension-of-scalars
presentation, the sheafified canonical connection is still
`D ⊗ x ↦ ∇ᶜᵃⁿ_D x`. -/
lemma directCanonicalConnectionHom_tmul_unit
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op U)) :
    (directCanonicalConnectionHom (p := p) X M).hom.app (.op U)
        (connectionTmul X
          ((directFrobeniusPullbackFunctor (p := p) X).obj M) U D
          ((CategoryTheory.toSheafify
            (Opens.grothendieckTopology X.scheme)
            (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app
              (.op U) x)) =
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme)
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app
          (.op U) (directCanonicalNablaAdd (p := p) X M (.op U) D x) := by
  let P := (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
  let t := connectionTensorPureOf X P U D x
  have hc := connectionTensorSheafificationIso_hom_unit X P (.op U) t
  have hm :
      (connectionTensorPresheafMap X
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme) P)).app (.op U) t =
        connectionTensorPureOf X
          ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
            AddCommGrpCat.{u}).obj P).obj U D
          ((CategoryTheory.toSheafify
            (Opens.grothendieckTopology X.scheme) P).app (.op U) x) :=
    connectionTensorPresheafMap_pure X
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P) U D x
  have hc' :
      (connectionTensorSheafificationIso X P).hom.hom.app (.op U)
          ((connectionTensorSheafUnit X P).app (.op U) t) =
        (connectionTensorSheafUnit X
          ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
            AddCommGrpCat.{u}).obj P).obj).app (.op U)
          (connectionTensorPureOf X
            ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
              AddCommGrpCat.{u}).obj P).obj U D
            ((CategoryTheory.toSheafify
              (Opens.grothendieckTopology X.scheme) P).app (.op U) x)) :=
    hc.trans (congrArg
      ((connectionTensorSheafUnit X
        ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
          AddCommGrpCat.{u}).obj P).obj).app (.op U)) hm)
  change ((connectionTensorSheafificationIso X P).inv.hom.app (.op U) ≫
      (sheafifiedDirectCanonicalAction (p := p) X M).hom.app (.op U))
        ((connectionTensorSheafUnit X
          ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
            AddCommGrpCat.{u}).obj P).obj).app (.op U)
          (connectionTensorPureOf X
            ((presheafToSheaf (Opens.grothendieckTopology X.scheme)
              AddCommGrpCat.{u}).obj P).obj U D
            ((CategoryTheory.toSheafify
              (Opens.grothendieckTopology X.scheme) P).app (.op U) x))) = _
  rw [← hc']
  change (sheafifiedDirectCanonicalAction (p := p) X M).hom.app (.op U)
      ((connectionTensorSheafificationIso X P).inv.hom.app (.op U)
        ((connectionTensorSheafificationIso X P).hom.hom.app (.op U)
          ((connectionTensorSheafUnit X P).app (.op U) t))) = _
  have hi := congrArg (fun q ↦ q.hom.app (.op U))
    (Iso.hom_inv_id (connectionTensorSheafificationIso X P))
  have hit := congrArg
    (fun q ↦ q.hom ((connectionTensorSheafUnit X P).app (.op U) t)) hi
  change (connectionTensorSheafificationIso X P).inv.hom.app (.op U)
      ((connectionTensorSheafificationIso X P).hom.hom.app (.op U)
        ((connectionTensorSheafUnit X P).app (.op U) t)) =
    (connectionTensorSheafUnit X P).app (.op U) t at hit
  rw [hit]
  change (sheafifiedDirectCanonicalAction (p := p) X M).hom.app (.op U)
      ((connectionTensorSheafUnit X P).app (.op U) t) = _
  have hn := (sheafificationAdjunction
    (Opens.grothendieckTopology X.scheme) AddCommGrpCat.{u}).unit.naturality
      (directCanonicalActionPresheaf (p := p) X M)
  have hnU := congrArg (fun q ↦ q.app (.op U)) hn
  have hnt := congrArg (fun q ↦ q.hom t) hnU
  change (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.scheme) P).app (.op U)
      ((directCanonicalAction (p := p) X M).app (.op U) t) =
    (sheafifiedDirectCanonicalAction (p := p) X M).hom.app (.op U)
      ((connectionTensorSheafUnit X P).app (.op U) t) at hnt
  exact hnt.symm.trans (congrArg
    ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.scheme) P).app (.op U))
    (directCanonicalAction_tmul (p := p) X M (.op U) D x))

/-- Contract the sheafified canonical connection with a vector field. -/
noncomputable def directCanonicalSheafNabla
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U)
    (m : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
    Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U) :=
  (directCanonicalConnectionHom (p := p) X M).hom.app (.op U)
    (connectionTmul X
      ((directFrobeniusPullbackFunctor (p := p) X).obj M) U D m)

lemma directCanonicalSheafNabla_unit
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op U)) :
    directCanonicalSheafNabla (p := p) X M U D
        ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme)
          (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app
            (.op U) x) =
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme)
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app
          (.op U) (directCanonicalNablaAdd (p := p) X M (.op U) D x) :=
  directCanonicalConnectionHom_tmul_unit (p := p) X M U D x

/-- The contracted sheafified canonical connection commutes with
restriction. -/
lemma directCanonicalSheafNabla_restrict
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U)
    (m : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).presheaf.map
        (homOfLE hVU).op
        (directCanonicalSheafNabla (p := p) X M U D m) =
      directCanonicalSheafNabla (p := p) X M V (D.restrict hVU)
        (((directFrobeniusPullbackFunctor (p := p) X).obj M).presheaf.map
          (homOfLE hVU).op m) := by
  have hn := CategoryTheory.congr_fun
    ((directCanonicalConnectionHom (p := p) X M).hom.naturality
      (homOfLE hVU).op)
    (connectionTmul X
      ((directFrobeniusPullbackFunctor (p := p) X).obj M) U D m)
  change (directCanonicalConnectionHom (p := p) X M).hom.app (.op V)
      ((connectionTensor X
        ((directFrobeniusPullbackFunctor (p := p) X).obj M)).obj.map
          (homOfLE hVU).op
          (connectionTmul X
            ((directFrobeniusPullbackFunctor (p := p) X).obj M) U D m)) =
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
      (homOfLE hVU).op
      ((directCanonicalConnectionHom (p := p) X M).hom.app (.op U)
        (connectionTmul X
          ((directFrobeniusPullbackFunctor (p := p) X).obj M) U D m)) at hn
  exact hn.symm.trans (congrArg
    ((directCanonicalConnectionHom (p := p) X M).hom.app (.op V))
    (connectionTmul_restrict X
      ((directFrobeniusPullbackFunctor (p := p) X).obj M) hVU D m))

set_option backward.isDefEq.respectTransparency false in
/-- To prove an equality of sections of the sheafified direct pullback, it
is enough to prove it after every restriction on which the distinguished
section is represented by a section of the original presheaf. -/
lemma directFrobeniusPullback_eq_of_local_representation
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens)
    (m s t : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U))
    (h : ∀ (V : X.scheme.Opens) (hVU : V ≤ U)
      (y : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)),
      (CategoryTheory.toSheafify
          (Opens.grothendieckTopology X.scheme)
          (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app
            (.op V) y =
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op m →
      ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op s =
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op t) : s = t := by
  let P := (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
  let F := (directFrobeniusPullbackFunctor (p := p) X).obj M
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.scheme.ringCatSheaf).obj F) U
  intro x hx
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X.scheme)
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P) := inferInstance
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P)).1 hsurj U m x hx
  change (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.scheme) P).app (.op V) y =
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
      (homOfLE hVU).op m at hy
  apply TopCat.Presheaf.germ_ext F.presheaf V hxV
    (homOfLE hVU) (homOfLE hVU)
  exact h V hVU y hy

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified canonical connection is linear in the vector-field
argument. -/
lemma directCanonicalSheafNabla_smul_vectorField
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (a : Γ(X.scheme, U))
    (D : X.VectorField U)
    (m : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
    directCanonicalSheafNabla (p := p) X M U (a • D) m =
      a • directCanonicalSheafNabla (p := p) X M U D m := by
  apply directFrobeniusPullback_eq_of_local_representation
    (p := p) X M U m
  intro V hVU y hy
  have hD : (a • D).restrict hVU =
      X.scheme.presheaf.map (homOfLE hVU).op a • D.restrict hVU :=
    vectorFieldAbPresheaf_map_smul X (homOfLE hVU).op a D
  let aV := X.scheme.presheaf.map (homOfLE hVU).op a
  have hlocal : directCanonicalSheafNabla (p := p) X M V
      ((a • D).restrict hVU)
        (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op m) =
      aV • directCanonicalSheafNabla (p := p) X M V (D.restrict hVU)
        (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op m) := by
    rw [← hy, hD, directCanonicalSheafNabla_unit,
      directCanonicalSheafNabla_unit]
    rw [directCanonicalNablaAdd_smul_vectorField]
    exact directFrobeniusPullbackSheafificationUnit_smul
      (p := p) X M (.op V) aV
        (directCanonicalNablaAdd (p := p) X M (.op V) (D.restrict hVU) y)
  calc
    _ = directCanonicalSheafNabla (p := p) X M V
          ((a • D).restrict hVU)
          (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op m) :=
      directCanonicalSheafNabla_restrict (p := p) X M hVU (a • D) m
    _ = aV • directCanonicalSheafNabla (p := p) X M V (D.restrict hVU)
          (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op m) := hlocal
    _ = aV • ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op
          (directCanonicalSheafNabla (p := p) X M U D m) :=
      congrArg (fun z ↦ aV • z)
        (directCanonicalSheafNabla_restrict (p := p) X M hVU D m).symm
    _ = _ := (PresheafOfModules.map_smul
      ((directFrobeniusPullbackFunctor (p := p) X).obj M).val
      (homOfLE hVU).op a
      (directCanonicalSheafNabla (p := p) X M U D m)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified canonical connection satisfies the Leibniz rule on all
sections, not only on sections coming globally from the defining
presheaf. -/
lemma directCanonicalSheafNabla_leibniz
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D : X.VectorField U)
    (a : Γ(X.scheme, U))
    (m : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
    directCanonicalSheafNabla (p := p) X M U D (a • m) =
      a • directCanonicalSheafNabla (p := p) X M U D m + D.act a • m := by
  apply directFrobeniusPullback_eq_of_local_representation
    (p := p) X M U m
  intro V hVU y hy
  let P := (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
  let aV : Γ(X.scheme, V) := X.scheme.presheaf.map (homOfLE hVU).op a
  let mV : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) :=
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
      (homOfLE hVU).op m
  let η (z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) :=
    (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.scheme) P).app (.op V) z
  have hmV : mV = η y := hy.symm
  have hDa : X.scheme.presheaf.map (homOfLE hVU).op (D.act a) =
      (D.restrict hVU).act aV := D.compatible le_rfl hVU a
  have hη_smul (b : Γ(X.scheme, V))
      (z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      η ((show X.scheme.ringCatSheaf.obj.obj (.op V) from b) • z) =
        b • η z := by
    exact directFrobeniusPullbackSheafificationUnit_smul
      (p := p) X M (.op V) b z
  have hη_add
      (z w : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      η (z + w) = η z + η w := by
    exact map_add
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P).app (.op V)).hom z w
  have hnabla_unit (G : X.VectorField V)
      (z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      directCanonicalSheafNabla (p := p) X M V G (η z) =
        η (directCanonicalNablaAdd (p := p) X M (.op V) G z) :=
    directCanonicalSheafNabla_unit (p := p) X M V G z
  have hmap_smul (b : Γ(X.scheme, U))
      (z : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
      (show Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) from
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op (b • z)) =
        (show Γ(X.scheme, V) from
          X.scheme.presheaf.map (homOfLE hVU).op b) •
          (show Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) from
            ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
              (homOfLE hVU).op z) :=
    PresheafOfModules.map_smul
      ((directFrobeniusPullbackFunctor (p := p) X).obj M).val
      (homOfLE hVU).op b z
  have hlocal : directCanonicalSheafNabla (p := p) X M V
      (D.restrict hVU) (aV • mV) =
    aV • directCanonicalSheafNabla (p := p) X M V (D.restrict hVU) mV +
      (D.restrict hVU).act aV • mV := by
    let DV := D.restrict hVU
    let z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V) :=
      directCanonicalNablaAdd (p := p) X M (.op V) DV y
    have hpre := directCanonicalNablaAdd_leibniz
      (p := p) X M (.op V) DV aV y
    calc
      _ = directCanonicalSheafNabla (p := p) X M V DV (aV • η y) :=
        congrArg (directCanonicalSheafNabla (p := p) X M V DV)
          (congrArg (fun q ↦ aV • q) hmV)
      _ = directCanonicalSheafNabla (p := p) X M V DV
          (η ((show X.scheme.ringCatSheaf.obj.obj (.op V) from aV) • y)) :=
        congrArg (directCanonicalSheafNabla (p := p) X M V DV)
          (hη_smul aV y).symm
      _ = η (directCanonicalNablaAdd (p := p) X M (.op V) DV
          ((show X.scheme.ringCatSheaf.obj.obj (.op V) from aV) • y)) :=
        hnabla_unit DV _
      _ = η ((show X.scheme.ringCatSheaf.obj.obj (.op V) from aV) • z +
          (show X.scheme.ringCatSheaf.obj.obj (.op V) from DV.act aV) •
            (show (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)
              from y)) := congrArg η hpre
      _ = η ((show X.scheme.ringCatSheaf.obj.obj (.op V) from aV) • z) +
          η ((show X.scheme.ringCatSheaf.obj.obj (.op V) from DV.act aV) •
            (show (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)
              from y)) := hη_add _ _
      _ = aV • η z + DV.act aV • η y :=
        congrArg₂ (fun q r ↦ q + r) (hη_smul aV z) (hη_smul (DV.act aV) y)
      _ = aV • directCanonicalSheafNabla (p := p) X M V DV (η y) +
          DV.act aV • η y := congrArg
        (fun q ↦ aV • q + DV.act aV • η y) (hnabla_unit DV y).symm
      _ = _ := congrArg₂ (fun q r ↦
          aV • directCanonicalSheafNabla (p := p) X M V DV q +
            DV.act aV • r) hmV.symm hmV.symm
  calc
    _ = directCanonicalSheafNabla (p := p) X M V (D.restrict hVU)
          (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op (a • m)) :=
      directCanonicalSheafNabla_restrict (p := p) X M hVU D (a • m)
    _ = directCanonicalSheafNabla (p := p) X M V (D.restrict hVU)
          (aV • mV) := congrArg
      (directCanonicalSheafNabla (p := p) X M V (D.restrict hVU))
      (PresheafOfModules.map_smul
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val
        (homOfLE hVU).op a m)
    _ = aV • directCanonicalSheafNabla (p := p) X M V
          (D.restrict hVU) mV + (D.restrict hVU).act aV • mV := hlocal
    _ = aV • (show Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) from
          ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op
            (directCanonicalSheafNabla (p := p) X M U D m)) +
        (show Γ(X.scheme, V) from
          X.scheme.presheaf.map (homOfLE hVU).op (D.act a)) • mV := by
      rw [hDa]
      exact congrArg (fun z ↦ aV • z + (D.restrict hVU).act aV • mV)
        (directCanonicalSheafNabla_restrict (p := p) X M hVU D m).symm
    _ = ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op
          (a • directCanonicalSheafNabla (p := p) X M U D m) +
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op (D.act a • m) := by
      exact congrArg₂ (fun q r ↦ q + r)
        (hmap_smul a (directCanonicalSheafNabla (p := p) X M U D m)).symm
        (hmap_smul (D.act a) m).symm
    _ = _ := by rw [map_add]

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified canonical connection is flat on every open. -/
lemma directCanonicalSheafNabla_flat
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opens) (D E : X.VectorField U)
    (m : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, U)) :
    directCanonicalSheafNabla (p := p) X M U ⁅D, E⁆ m =
      directCanonicalSheafNabla (p := p) X M U D
          (directCanonicalSheafNabla (p := p) X M U E m) -
        directCanonicalSheafNabla (p := p) X M U E
          (directCanonicalSheafNabla (p := p) X M U D m) := by
  apply directFrobeniusPullback_eq_of_local_representation
    (p := p) X M U m
  intro V hVU y hy
  let P := (directFrobeniusPullbackPresheaf (p := p) X M).presheaf
  let DV := D.restrict hVU
  let EV := E.restrict hVU
  let mV : Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) :=
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
      (homOfLE hVU).op m
  let η (z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      Γ((directFrobeniusPullbackFunctor (p := p) X).obj M, V) :=
    (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.scheme) P).app (.op V) z
  have hmV : mV = η y := hy.symm
  have hbracket : ⁅D, E⁆.restrict hVU = ⁅DV, EV⁆ := by
    ext W hW b
    rfl
  have hη_sub
      (z w : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      η (z - w) = η z - η w := by
    exact map_sub
      ((CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme) P).app (.op V)).hom z w
  have hnabla_unit (G : X.VectorField V)
      (z : (directFrobeniusPullbackPresheaf (p := p) X M).obj (.op V)) :
      directCanonicalSheafNabla (p := p) X M V G (η z) =
        η (directCanonicalNablaAdd (p := p) X M (.op V) G z) :=
    directCanonicalSheafNabla_unit (p := p) X M V G z
  have hlocal : directCanonicalSheafNabla (p := p) X M V
      (⁅D, E⁆.restrict hVU) mV =
    directCanonicalSheafNabla (p := p) X M V DV
        (directCanonicalSheafNabla (p := p) X M V EV mV) -
      directCanonicalSheafNabla (p := p) X M V EV
        (directCanonicalSheafNabla (p := p) X M V DV mV) := by
    let zE := directCanonicalNablaAdd (p := p) X M (.op V) EV y
    let zD := directCanonicalNablaAdd (p := p) X M (.op V) DV y
    have hpre := directCanonicalNablaAdd_flat (p := p) X M (.op V) DV EV y
    calc
      _ = directCanonicalSheafNabla (p := p) X M V ⁅DV, EV⁆ (η y) :=
        congrArg₂ (fun G q ↦ directCanonicalSheafNabla (p := p) X M V G q)
          hbracket hmV
      _ = η (directCanonicalNablaAdd (p := p) X M (.op V) ⁅DV, EV⁆ y) :=
        hnabla_unit _ y
      _ = η (directCanonicalNablaAdd (p := p) X M (.op V) DV zE -
          directCanonicalNablaAdd (p := p) X M (.op V) EV zD) :=
        congrArg η hpre
      _ = η (directCanonicalNablaAdd (p := p) X M (.op V) DV zE) -
          η (directCanonicalNablaAdd (p := p) X M (.op V) EV zD) :=
        hη_sub _ _
      _ = directCanonicalSheafNabla (p := p) X M V DV (η zE) -
          directCanonicalSheafNabla (p := p) X M V EV (η zD) :=
        congrArg₂ (fun q r ↦ q - r) (hnabla_unit DV zE).symm
          (hnabla_unit EV zD).symm
      _ = directCanonicalSheafNabla (p := p) X M V DV
            (directCanonicalSheafNabla (p := p) X M V EV (η y)) -
          directCanonicalSheafNabla (p := p) X M V EV
            (directCanonicalSheafNabla (p := p) X M V DV (η y)) :=
        congrArg₂ (fun q r ↦
          directCanonicalSheafNabla (p := p) X M V DV q -
            directCanonicalSheafNabla (p := p) X M V EV r)
          (hnabla_unit EV y).symm (hnabla_unit DV y).symm
      _ = _ := congrArg₂ (fun q r ↦
          directCanonicalSheafNabla (p := p) X M V DV
              (directCanonicalSheafNabla (p := p) X M V EV q) -
            directCanonicalSheafNabla (p := p) X M V EV
              (directCanonicalSheafNabla (p := p) X M V DV r))
        hmV.symm hmV.symm
  have hEres := directCanonicalSheafNabla_restrict (p := p) X M hVU E m
  have hDres := directCanonicalSheafNabla_restrict (p := p) X M hVU D m
  have hDEres := directCanonicalSheafNabla_restrict (p := p) X M hVU D
    (directCanonicalSheafNabla (p := p) X M U E m)
  have hEDres := directCanonicalSheafNabla_restrict (p := p) X M hVU E
    (directCanonicalSheafNabla (p := p) X M U D m)
  calc
    _ = directCanonicalSheafNabla (p := p) X M V
          (⁅D, E⁆.restrict hVU) mV :=
      directCanonicalSheafNabla_restrict (p := p) X M hVU ⁅D, E⁆ m
    _ = directCanonicalSheafNabla (p := p) X M V DV
          (directCanonicalSheafNabla (p := p) X M V EV mV) -
        directCanonicalSheafNabla (p := p) X M V EV
          (directCanonicalSheafNabla (p := p) X M V DV mV) := hlocal
    _ = directCanonicalSheafNabla (p := p) X M V DV
          (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op (directCanonicalSheafNabla (p := p) X M U E m)) -
        directCanonicalSheafNabla (p := p) X M V EV
          (((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
            (homOfLE hVU).op (directCanonicalSheafNabla (p := p) X M U D m)) :=
      congrArg₂ (fun q r ↦
        directCanonicalSheafNabla (p := p) X M V DV q -
          directCanonicalSheafNabla (p := p) X M V EV r)
        hEres.symm hDres.symm
    _ = ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op
          (directCanonicalSheafNabla (p := p) X M U D
            (directCanonicalSheafNabla (p := p) X M U E m)) -
        ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.map
          (homOfLE hVU).op
          (directCanonicalSheafNabla (p := p) X M U E
            (directCanonicalSheafNabla (p := p) X M U D m)) :=
      congrArg₂ (fun q r ↦ q - r) hDEres.symm hEDres.symm
    _ = _ := by rw [map_sub]

/-- The sheafified direct Frobenius pullback of a quasicoherent module is
quasicoherent. -/
noncomputable instance directFrobeniusPullback_isQuasicoherent
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    [M.IsQuasicoherent] :
    ((directFrobeniusPullbackFunctor (p := p) X).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.scheme.ringCatSheaf).prop_of_iso
    (directFrobeniusPullbackObjIso (p := p) X M).symm inferInstance

/-- The canonical flat connection on the Frobenius pullback of a
quasicoherent module, bundled as an actual `IntegrableConnection`. -/
noncomputable def directCanonicalConnection
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    [M.IsQuasicoherent] : X.IntegrableConnection where
  carrier := (directFrobeniusPullbackFunctor (p := p) X).obj M
  carrier_quasicoherent := inferInstance
  nablaHom := directCanonicalConnectionHom (p := p) X M
  nabla_smul_vectorField U a D m :=
    directCanonicalSheafNabla_smul_vectorField (p := p) X M U a D m
  leibniz_tmul U D a m :=
    directCanonicalSheafNabla_leibniz (p := p) X M U D a m
  flat_tmul U D E m :=
    directCanonicalSheafNabla_flat (p := p) X M U D E m

end

end LSZ.SmoothScheme
