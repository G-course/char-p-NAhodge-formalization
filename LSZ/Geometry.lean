import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The geometric input for the Lan--Sheng--Zuo construction

The public geometric input in this file consists of a field `k` and one
smooth separated scheme over `Spec k`.  In particular, no cotangent sheaf,
tangent sheaf, anchor, bracket, or restricted power operation is supplied by
the caller.

The relative cotangent sheaf is constructed canonically.  First we form the
map from the constant presheaf `k` to the structure presheaf of `X`; then we
apply mathlib's objectwise Kähler-differential construction and sheafify the
result as a presheaf of modules.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

/-- A smooth separated `k`-scheme, bundled as a single geometric object.

The structure morphism is part of what it means to be a scheme over `k`;
the last two fields are propositions asserting smoothness and separatedness,
not extra differential-geometric structures. -/
structure SmoothScheme (k : Type u) [Field k] where
  toScheme : AlgebraicGeometry.Scheme.{u}
  structureMap : toScheme ⟶ AlgebraicGeometry.Spec (.of k)
  smooth : AlgebraicGeometry.Smooth structureMap
  separated : AlgebraicGeometry.IsSeparated structureMap

namespace SmoothScheme

variable {k : Type u} [Field k] (X : SmoothScheme k)

/-- The underlying scheme of a bundled smooth separated `k`-scheme. -/
abbrev scheme : AlgebraicGeometry.Scheme.{u} := X.toScheme

instance : AlgebraicGeometry.Smooth X.structureMap := X.smooth

instance : AlgebraicGeometry.IsSeparated X.structureMap := X.separated

/-- The constant presheaf with value `k` on the category of opens of `X`. -/
def constantBasePresheaf : X.scheme.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const X.scheme.Opensᵒᵖ).obj (.of k)

/-- The canonical morphism from the constant presheaf `k` to `𝒪_X`.

On an open `U`, this is the structure map on global functions followed by
restriction from `X` to `U`. -/
noncomputable def baseToStructureSheaf :
    X.constantBasePresheaf ⟶ X.scheme.presheaf where
  app U :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (.of k)).inv ≫
      X.structureMap.appLE ⊤ U.unop le_top
  naturality {U V} i := by
    simp only [constantBasePresheaf, Functor.const_obj_obj,
      Functor.const_obj_map, Category.id_comp]
    rw [Category.assoc, X.structureMap.appLE_map
      (U := (⊤ : (AlgebraicGeometry.Spec (.of k)).Opens))
      (V := U.unop) (V' := V.unop) le_top i]

/-- The objectwise presheaf of relative Kähler differentials of `X/k`.

Its restriction maps are supplied by the functoriality of Kähler
differentials in mathlib; they are not additional geometric input. -/
noncomputable def cotangentPresheaf : X.scheme.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    X.baseToStructureSheaf

/-- The relative cotangent sheaf `Ω¹_{X/k}` obtained by sheafifying the
canonical presheaf of relative Kähler differentials. -/
noncomputable def cotangent : X.scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.scheme.ringCatSheaf.obj)).obj
    X.cotangentPresheaf

end SmoothScheme

end LSZ
