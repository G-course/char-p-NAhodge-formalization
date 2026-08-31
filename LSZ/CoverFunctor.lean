import LSZ.AffineFrobenius
import LSZ.GlobalFunctor

/-!
# The LSZ functor from an affine Frobenius atlas

Each member of an `AffineFrobeniusAtlas` is first converted to a genuine
`W₂(k)`-lifting with a global Frobenius lifting.  The local construction
forgets the source nilpotence proof and then applies the same unrestricted
global functor from `LSZ.GlobalFunctor`.

Mathlib does not yet contain descent for quasi-coherent modules equipped
with connection.  `DescentData` states the output and the exact descent
identities of that missing primitive.  It deliberately does not contain a
functor to flat objects: the object, morphism, p-curvature proof, and all
functor laws are constructed below.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {X : AlgebraicGeometry.Scheme.{u}}
variable {L : W₂Lift (p := p) (k := k) X}

namespace Atlas

open SchemeObject

variable (A : AffineFrobeniusAtlas L)

/-- The local `W₂(k)`-lifting carried by the `i`-th member of an atlas. -/
noncomputable abbrev localW₂Lift (i : A.cover.I₀) :
    W₂Lift (p := p) (k := k) (A.chart i) :=
  (A.localLift i).toW₂Lift

/-- The local Frobenius lifting, in the format consumed by the global LSZ
construction. -/
noncomputable abbrev localGlobalFrobeniusLift (i : A.cover.I₀) :
    GlobalFrobeniusLift (A.chart i) (localW₂Lift A i) :=
  (A.localLift i).toGlobalFrobeniusLift

/-- Local Cartier input attached to an affine Frobenius atlas.

`restrictHiggs` and `tangentIso` are the restriction identifications from
`X` to an affine member.  `divided` is `d F̃ᵢ/[p]` together with the local
Cartier identities. -/
structure LocalCartierData (T : RestrictedTangentSheaf X p) where
  localTangent (i : A.cover.I₀) : RestrictedTangentSheaf (A.chart i) p
  tangentIso (i : A.cover.I₀) :
    T.tangent.restrict (A.cover.f i) ≅ (localTangent i).tangent
  restrictHiggs (i : A.cover.I₀) :
    SchemeObject.NilpotentHiggs T ⥤
      SchemeObject.NilpotentHiggs (localTangent i)
  restrictHiggsCarrierIso (E : SchemeObject.NilpotentHiggs T)
      (i : A.cover.I₀) :
    ((restrictHiggs i).obj E).carrier ≅ E.carrier.restrict (A.cover.f i)
  restrictHiggsCarrierIso_natural
      {E G : SchemeObject.NilpotentHiggs T} (f : E ⟶ G)
      (i : A.cover.I₀) :
    (restrictHiggsCarrierIso E i).hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor
          (A.cover.f i)).map f.hom =
      ((restrictHiggs i).map f).hom ≫
        (restrictHiggsCarrierIso G i).hom
  divided (i : A.cover.I₀) :
    (localGlobalFrobeniusLift A i).DividedDifferentialData (localTangent i)

namespace LocalCartierData

variable {A : AffineFrobeniusAtlas L} {T : RestrictedTangentSheaf X p}

/-- The actual LSZ connection functor on the `i`-th affine chart.

The source is nilpotent because later overlap gluing uses truncated
exponentials.  The local connection formula itself does not use that proof:
after restriction we forget nilpotence and invoke the same unrestricted
global Frobenius-lift functor. -/
noncomputable def localFunctor (D : LocalCartierData A T) (i : A.cover.I₀) :
    SchemeObject.NilpotentHiggs T ⥤
      SchemeObject.IntegrableConnection (D.localTangent i) :=
  D.restrictHiggs i ⋙
    SchemeObject.nilpotentHiggsForget (D.localTangent i) ⋙
    (localGlobalFrobeniusLift A i).globalLSZFunctor
      (D.localTangent i) (D.divided i)

end LocalCartierData

/-- Descent of the affine LSZ constructions to `X`.

The first four fields give the descended quasi-coherent module and its
local identifications with the local LSZ transforms.  The remaining fields
are exactly the restriction, Leibniz, flatness, naturality and Cartier
`p`-curvature identities checked locally in the LSZ proof.
-/
structure DescentData (T : RestrictedTangentSheaf X p)
    extends LocalCartierData A T where
  carrier : SchemeObject.NilpotentHiggs T ⥤ X.Modules
  carrier_quasicoherent (E : SchemeObject.NilpotentHiggs T) :
    (carrier.obj E).IsQuasicoherent
  localCarrierIso (E : SchemeObject.NilpotentHiggs T) (i : A.cover.I₀) :
    (carrier.obj E).restrict (A.cover.f i) ≅
      ((toLocalCartierData.localFunctor i).obj E).carrier
  localCarrierIso_natural
      {E G : SchemeObject.NilpotentHiggs T} (f : E ⟶ G)
      (i : A.cover.I₀) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (A.cover.f i)).map (carrier.map f) ≫
        (localCarrierIso G i).hom =
      (localCarrierIso E i).hom ≫
        ((toLocalCartierData.localFunctor i).map f).hom

  nabla (E : SchemeObject.NilpotentHiggs T) (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)]
      Module.End ℤ Γ(carrier.obj E, U)
  nabla_restrict (E : SchemeObject.NilpotentHiggs T)
      {U V : X.Opens} (i : U ⟶ V) (D : Γ(T.tangent, V))
      (m : Γ(carrier.obj E, V)) :
    (carrier.obj E).presheaf.map i.op (nabla E V D m) =
      nabla E U (T.tangent.presheaf.map i.op D)
        ((carrier.obj E).presheaf.map i.op m)
  nabla_leibniz (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
      (D : Γ(T.tangent, U)) (a : Γ(X, U)) (m : Γ(carrier.obj E, U)) :
    nabla E U D (a • m) =
      a • nabla E U D m + T.anchor U D a • m
  nabla_flat (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
      (D E' : Γ(T.tangent, U)) (m : Γ(carrier.obj E, U)) :
    nabla E U (T.bracket U D E') m =
      nabla E U D (nabla E U E' m) -
        nabla E U E' (nabla E U D m)
  nabla_natural {E G : SchemeObject.NilpotentHiggs T} (f : E ⟶ G)
      (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(carrier.obj E, U)) :
    (carrier.map f).app U (nabla E U D m) =
      nabla G U D ((carrier.map f).app U m)

  /-- After transport by the descent trivialization, the global connection
  is the local LSZ connection produced from `d F̃ᵢ/[p]`. -/
  local_connection_formula (E : SchemeObject.NilpotentHiggs T)
      (i : A.cover.I₀) (V : (A.chart i).Opens)
      (v : Γ((toLocalCartierData.localTangent i).tangent, V))
      (m : Γ(((toLocalCartierData.localFunctor i).obj E).carrier, V)) :
    (localCarrierIso E i).hom.app V
        (((carrier.obj E).restrictAppIso (A.cover.f i) V).inv
          (nabla E ((A.cover.f i) ''ᵁ V)
            ((T.tangent.restrictAppIso (A.cover.f i) V).hom
              ((toLocalCartierData.tangentIso i).inv.app V v))
            (((carrier.obj E).restrictAppIso (A.cover.f i) V).hom
              ((localCarrierIso E i).inv.app V m)))) =
      ((toLocalCartierData.localFunctor i).obj E).nabla V v m

  pCurvatureModel (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
      (D : Γ(T.tangent, U)) : Module.End ℤ Γ(carrier.obj E, U)
  pCurvature_formula (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
      (D : Γ(T.tangent, U)) :
    (nabla E U D) ^ p - nabla E U (T.pPow U D) =
      pCurvatureModel E U D
  pCurvatureModel_nilpotent (E : SchemeObject.NilpotentHiggs T)
      (U : X.Opens) :
    IsWordNilpotent p (fun D m ↦ pCurvatureModel E U D m)

namespace DescentData

variable {A : AffineFrobeniusAtlas L} {T : RestrictedTangentSheaf X p}

/-- The descended integrable connection. -/
noncomputable def connection (D : DescentData A T)
    (E : SchemeObject.NilpotentHiggs T) : SchemeObject.IntegrableConnection T where
  carrier := D.carrier.obj E
  carrier_quasicoherent := D.carrier_quasicoherent E
  nabla := D.nabla E
  nabla_restrict := D.nabla_restrict E
  leibniz := D.nabla_leibniz E
  flat := D.nabla_flat E

lemma connection_pCurvature (D : DescentData A T)
    (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
    (v : Γ(T.tangent, U)) :
    SchemeObject.pCurvature (D.connection E) U v =
      D.pCurvatureModel E U v := by
  change (D.nabla E U v) ^ p - D.nabla E U (T.pPow U v) =
    D.pCurvatureModel E U v
  exact D.pCurvature_formula E U v

/-- Object part of the cover-dependent LSZ transform. -/
noncomputable def obj (D : DescentData A T)
    (E : SchemeObject.NilpotentHiggs T) : SchemeObject.NilpotentFlat T where
  toIntegrableConnection := D.connection E
  nilpotentPCurvature U := by
    have h :
        (fun v m ↦ SchemeObject.pCurvature (D.connection E) U v m) =
          (fun v m ↦ D.pCurvatureModel E U v m) := by
      funext v m
      rw [D.connection_pCurvature E U v]
      rfl
    rw [h]
    exact D.pCurvatureModel_nilpotent E U

/-- Morphism part of the cover-dependent LSZ transform. -/
noncomputable def map (D : DescentData A T)
    {E G : SchemeObject.NilpotentHiggs T} (f : E ⟶ G) :
    D.obj E ⟶ D.obj G where
  hom := D.carrier.map f
  horizontal U v m := D.nabla_natural f U v m

/-- The LSZ functor attached to one affine cover with local Frobenius
liftings. -/
noncomputable def lszFunctor (D : DescentData A T) :
    SchemeObject.NilpotentHiggs T ⥤ SchemeObject.NilpotentFlat T where
  obj := D.obj
  map := D.map
  map_id E := by
    apply SchemeObject.FlatHom.ext
    exact D.carrier.map_id E
  map_comp f g := by
    apply SchemeObject.FlatHom.ext
    exact D.carrier.map_comp f g

end DescentData

end Atlas

end LSZ
