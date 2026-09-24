import LSZ.ExtensionScalars
import LSZ.FrobeniusPullback
import LSZ.StandardCanonicalConnection

/-!
# An objectwise presentation of Frobenius pullback

For absolute Frobenius the map of underlying spaces is the identity.  Its
pullback on module sheaves can therefore be presented by applying
`ModuleCat.extendScalars` along `a ↦ a ^ p` on every open and then
sheafifying.  This file keeps that concrete presentation available while
proving that it is naturally isomorphic to mathlib's
`Scheme.Modules.pullback`.

The concrete presentation is used to define the canonical Cartier
connection.  The public carrier remains mathlib's pullback; the natural
isomorphism below is the transport bridge.
-/

open CategoryTheory
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {p : ℕ} {k : Type u}
variable [Field k] [CharP k p] [Fact p.Prime]

/-- Absolute Frobenius as an endomorphism of the structure sheaf on the
unchanged site of opens. -/
noncomputable abbrev absoluteFrobeniusSheafEnd (X : LSZ.SmoothScheme k) :
    X.scheme.sheaf ⟶ X.scheme.sheaf :=
  ⟨{
    app := fun U ↦ CommRingCat.ofHom
      (algebraFrobenius k Γ(X.scheme, U.unop) p)
    naturality := by
      intro U V i
      ext a
      change (X.scheme.sheaf.obj.map i a) ^ p =
        X.scheme.sheaf.obj.map i (a ^ p)
      rw [map_pow] }⟩

/-- The structure-sheaf morphism occurring definitionally in mathlib's
absolute-Frobenius scheme morphism. -/
noncomputable def mathlibAbsoluteFrobeniusSheafEnd
    (X : LSZ.SmoothScheme k) : X.scheme.sheaf ⟶ X.scheme.sheaf :=
  ⟨AlgebraicGeometry.Scheme.frobeniusOnStructurePresheaf
    (p := p) X.scheme⟩

/-- The algebraic and scheme-theoretic presentations of Frobenius on the
structure sheaf coincide. -/
lemma absoluteFrobeniusSheafEnd_eq_mathlib
    (X : LSZ.SmoothScheme k) :
    absoluteFrobeniusSheafEnd (p := p) X =
      mathlibAbsoluteFrobeniusSheafEnd (p := p) X := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U a
  rfl

@[simp]
lemma absoluteFrobeniusSheafEnd_app_apply
    (X : LSZ.SmoothScheme k) (U : X.scheme.Opensᵒᵖ)
    (a : X.scheme.presheaf.obj U) :
    (absoluteFrobeniusSheafEnd (p := p) X).hom.app U a = a ^ p := by
  rfl

/-- On each open, the structure-sheaf map is the algebraic Frobenius used
by the affine canonical-connection construction. -/
lemma absoluteFrobeniusSheafEnd_app_hom
    (X : LSZ.SmoothScheme k) (U : X.scheme.Opensᵒᵖ) :
    ((absoluteFrobeniusSheafEnd (p := p) X).hom.app U).hom =
      algebraFrobenius k Γ(X.scheme, U.unop) p := by
  ext a
  rfl

/-- The objectwise extension-of-scalars presheaf
`U ↦ ᵊ_X(U) ⊗_{ᵊ_X(U),F} M(U)`. -/
noncomputable abbrev directFrobeniusPullbackPresheaf
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    X.scheme.PresheafOfModules :=
  CommRingSheaf.extensionPresheaf
    (absoluteFrobeniusSheafEnd (p := p) X).hom M.val

/-- Sheafify the objectwise extension-of-scalars presentation. -/
noncomputable abbrev directFrobeniusPullbackFunctor
    (X : LSZ.SmoothScheme k) :
    X.scheme.Modules ⥤ X.scheme.Modules :=
  CommRingSheaf.extensionScalarsFunctor.{u}
    (absoluteFrobeniusSheafEnd (p := p) X)

/-- The module-linear sheafification unit for the concrete Frobenius
pullback presheaf. -/
noncomputable def directFrobeniusPullbackSheafificationUnit
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    directFrobeniusPullbackPresheaf (p := p) X M ⟶
      ((directFrobeniusPullbackFunctor (p := p) X).obj M).val :=
  CommRingSheaf.directSheafificationUnit X.scheme.sheaf
    (directFrobeniusPullbackPresheaf (p := p) X M)

@[simp]
lemma directFrobeniusPullbackSheafificationUnit_app_apply
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    (directFrobeniusPullbackSheafificationUnit (p := p) X M).app U x =
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme)
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app U x :=
  rfl

lemma directFrobeniusPullbackSheafificationUnit_smul
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (a : X.scheme.presheaf.obj U)
    (x : (directFrobeniusPullbackPresheaf (p := p) X M).obj U) :
    (show ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.obj U from
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X.scheme)
        (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app U
          ((show X.scheme.ringCatSheaf.obj.obj U from a) • x)) =
      (show X.scheme.ringCatSheaf.obj.obj U from a) •
        (show ((directFrobeniusPullbackFunctor (p := p) X).obj M).val.obj U from
          (CategoryTheory.toSheafify
            (Opens.grothendieckTopology X.scheme)
            (directFrobeniusPullbackPresheaf (p := p) X M).presheaf).app U x) := by
  let a' : X.scheme.ringCatSheaf.obj.obj U := a
  change (directFrobeniusPullbackSheafificationUnit (p := p) X M).app U
      (a' • x) =
    a' • (directFrobeniusPullbackSheafificationUnit (p := p) X M).app U x
  exact map_smul
    ((directFrobeniusPullbackSheafificationUnit (p := p) X M).app U).hom a' x

/-- Objectwise extension followed by sheafification is naturally
mathlib's pullback along absolute Frobenius. -/
noncomputable def directFrobeniusPullbackIso
    (X : LSZ.SmoothScheme k) :
    directFrobeniusPullbackFunctor (p := p) X ≅
      AlgebraicGeometry.Scheme.Modules.pullback
        (X := X.scheme) (Y := X.scheme)
        (AlgebraicGeometry.Scheme.absoluteFrobenius
          (p := p) X.scheme) :=
  eqToIso (congrArg
      (fun alpha : X.scheme.sheaf ⟶ X.scheme.sheaf ↦
        CommRingSheaf.extensionScalarsFunctor.{u} alpha)
      (absoluteFrobeniusSheafEnd_eq_mathlib (p := p) X)) ≪≫
    CommRingSheaf.extensionPullbackIso.{u}
      (mathlibAbsoluteFrobeniusSheafEnd (p := p) X)

/-- Objectwise form of the comparison with mathlib pullback. -/
noncomputable def directFrobeniusPullbackObjIso
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules) :
    (directFrobeniusPullbackFunctor (p := p) X).obj M ≅
      FrobeniusPullback.carrier (p := p) X.scheme M :=
  (directFrobeniusPullbackIso (p := p) X).app M

/-- The canonical generator `1 ⊗ m` in the objectwise presentation. -/
noncomputable def directFrobeniusPullbackUnit
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (m : M.val.obj U) :
    (directFrobeniusPullbackPresheaf (p := p) X M).obj U :=
  CommRingSheaf.extensionUnit
    (absoluteFrobeniusSheafEnd (p := p) X).hom M.val U m

/-- The extension-of-scalars unit is the pure tensor `1 ⊗ m` in the
standard affine model. -/
lemma directFrobeniusPullbackUnit_eq_tmul_one
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (m : Γ(M, U.unop)) :
    directFrobeniusPullbackUnit (p := p) X M U m =
      StandardFrobeniusPullback.tmul k
        Γ(X.scheme, U.unop) Γ(M, U.unop) p 1 m := by
  unfold directFrobeniusPullbackUnit CommRingSheaf.extensionUnit
    StandardFrobeniusPullback.tmul
  exact ModuleCat.extendRestrictScalarsAdj_unit_app_apply
    (algebraFrobenius k Γ(X.scheme, U.unop) p) (M.val.obj U) m

@[simp]
lemma directFrobeniusPullbackUnit_add
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (m n : M.val.obj U) :
    directFrobeniusPullbackUnit (p := p) X M U (m + n) =
      directFrobeniusPullbackUnit (p := p) X M U m +
        directFrobeniusPullbackUnit (p := p) X M U n := by
  exact CommRingSheaf.extensionUnit_add
    (absoluteFrobeniusSheafEnd (p := p) X).hom M.val U m n

/-- A pure tensor `a ⊗ m` in the objectwise Frobenius pullback. -/
noncomputable def directFrobeniusPullbackTmul
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ) (a : X.scheme.presheaf.obj U)
    (m : M.val.obj U) :
    (directFrobeniusPullbackPresheaf (p := p) X M).obj U :=
  (((directFrobeniusPullbackPresheaf (p := p) X M).obj U).smul
    (show X.scheme.ringCatSheaf.obj.obj U from a)).hom
      (directFrobeniusPullbackUnit (p := p) X M U m)

/-- The exposed pure tensor agrees with the pure tensor in
`ModuleCat.extendScalars`. -/
lemma directFrobeniusPullbackTmul_eq_standard
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    (U : X.scheme.Opensᵒᵖ)
    (a : Γ(X.scheme, U.unop)) (m : Γ(M, U.unop)) :
    directFrobeniusPullbackTmul (p := p) X M U a m =
      StandardFrobeniusPullback.tmul k
        Γ(X.scheme, U.unop) Γ(M, U.unop) p a m := by
  unfold directFrobeniusPullbackTmul
  rw [directFrobeniusPullbackUnit_eq_tmul_one]
  exact (StandardFrobeniusPullback.smul_tmul
    k Γ(X.scheme, U.unop) Γ(M, U.unop) p a 1 m).trans
      (congrArg (fun b ↦ StandardFrobeniusPullback.tmul k
        Γ(X.scheme, U.unop) Γ(M, U.unop) p b m) (mul_one a))

lemma directFrobeniusPullbackTmul_map
    (X : LSZ.SmoothScheme k) (M : X.scheme.Modules)
    {U V : X.scheme.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.scheme.presheaf.obj U) (m : M.val.obj U) :
    (directFrobeniusPullbackPresheaf (p := p) X M).map i
        (directFrobeniusPullbackTmul (p := p) X M U a m) =
      directFrobeniusPullbackTmul (p := p) X M V
        (X.scheme.presheaf.map i a) (M.val.map i m) := by
  unfold directFrobeniusPullbackTmul
  let a' : X.scheme.ringCatSheaf.obj.obj U := a
  change (directFrobeniusPullbackPresheaf (p := p) X M).map i
      (a' • directFrobeniusPullbackUnit (p := p) X M U m) =
    X.scheme.ringCatSheaf.obj.map i a' •
      directFrobeniusPullbackUnit (p := p) X M V (M.val.map i m)
  rw [PresheafOfModules.map_smul]
  congr 1
  exact CommRingSheaf.extensionPresheafMap_unit
    (absoluteFrobeniusSheafEnd (p := p) X).hom M.val i m

end

end LSZ.SmoothScheme
