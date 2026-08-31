import LSZ.WittLift

/-!
# The global LSZ functor attached to a global Frobenius lifting

Let `F : X ⟶ X` be the Frobenius obtained by reducing a global
Frobenius lifting of a fixed `W₂(k)`-lifting.  For an arbitrary integrable
Higgs object `(E, θ)`, the LSZ connection on `F⁺E` is

`  ∇ = ∇ᶜᵃⁿ + (F⁺θ) ∘ ζ,       ζ = d F̃ / [p].`

No nilpotence hypothesis is needed when this one global Frobenius lifting
is fixed: there is no truncated-exponential gluing in this construction.

Mathlib does not yet define Kähler differentials of schemes or the divided
differential of a `W₂` Frobenius lift.  `GlobalCartierData` therefore
records precisely those missing constructions and their local identities.
The functor itself is *not* a field of this data: it is constructed below,
including flatness and the functor laws.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ}

namespace Global

open SchemeObject

/-- Pullback of an `𝒪_X`-module by the selected Frobenius endomorphism. -/
noncomputable abbrev frobeniusPullback (F : X ⟶ X) (M : X.Modules) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback F).obj M

/-- The underlying module of the global LSZ transform of a Higgs object. -/
noncomputable abbrev pulledBackCarrier
    {T : RestrictedTangentSheaf X p} (F : X ⟶ X)
    (E : SchemeObject.IntegrableHiggs T) : X.Modules :=
  frobeniusPullback F E.carrier

/-- Cartier-pullback data and the divided differential attached to a global
Frobenius lift.

* `canonicalNabla` is the canonical connection on `F⁺E`;
* `zeta` is contraction with `d F̃ / [p]`;
* `pullbackTheta` is the action of `F⁺θ` on `F⁺E`.

The remaining fields are the restriction, Leibniz, integrability and
naturality identities that these three geometric constructions satisfy.
They are stated sectionwise because mathlib currently has no sheaf of
Kähler differentials for schemes. -/
structure GlobalCartierData (T : RestrictedTangentSheaf X p) (F : X ⟶ X) where
  pullback_quasicoherent (M : X.Modules) :
    M.IsQuasicoherent → (frobeniusPullback F M).IsQuasicoherent

  canonicalNabla (E : SchemeObject.IntegrableHiggs T) (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End ℤ Γ(pulledBackCarrier F E, U)
  canonical_restrict (E : SchemeObject.IntegrableHiggs T) {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(T.tangent, V)) (m : Γ(pulledBackCarrier F E, V)) :
    (pulledBackCarrier F E).presheaf.map i.op (canonicalNabla E V D m) =
      canonicalNabla E U (T.tangent.presheaf.map i.op D)
        ((pulledBackCarrier F E).presheaf.map i.op m)
  canonical_leibniz (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
      (D : Γ(T.tangent, U)) (a : Γ(X, U)) (m : Γ(pulledBackCarrier F E, U)) :
    canonicalNabla E U D (a • m) =
      a • canonicalNabla E U D m + T.anchor U D a • m
  canonical_flat (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
      (D E' : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    canonicalNabla E U (T.bracket U D E') m =
      canonicalNabla E U D (canonicalNabla E U E' m) -
        canonicalNabla E U E' (canonicalNabla E U D m)

  zeta (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Γ(frobeniusPullback F T.tangent, U)
  zeta_restrict {U V : X.Opens} (i : U ⟶ V) (D : Γ(T.tangent, V)) :
    (frobeniusPullback F T.tangent).presheaf.map i.op (zeta V D) =
      zeta U (T.tangent.presheaf.map i.op D)

  pullbackTheta (E : SchemeObject.IntegrableHiggs T) (U : X.Opens) :
    Γ(frobeniusPullback F T.tangent, U) →ₗ[Γ(X, U)]
      Module.End ℤ Γ(pulledBackCarrier F E, U)
  pullbackTheta_restrict (E : SchemeObject.IntegrableHiggs T)
      {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(frobeniusPullback F T.tangent, V))
      (m : Γ(pulledBackCarrier F E, V)) :
    (pulledBackCarrier F E).presheaf.map i.op (pullbackTheta E V D m) =
      pullbackTheta E U ((frobeniusPullback F T.tangent).presheaf.map i.op D)
        ((pulledBackCarrier F E).presheaf.map i.op m)
  pullbackTheta_smul (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
      (D : Γ(frobeniusPullback F T.tangent, U))
      (a : Γ(X, U)) (m : Γ(pulledBackCarrier F E, U)) :
    pullbackTheta E U D (a • m) = a • pullbackTheta E U D m
  pullbackTheta_commutes (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
      (D E' : Γ(frobeniusPullback F T.tangent, U))
      (m : Γ(pulledBackCarrier F E, U)) :
    pullbackTheta E U D (pullbackTheta E U E' m) =
      pullbackTheta E U E' (pullbackTheta E U D m)

  canonical_natural {E G : SchemeObject.IntegrableHiggs T} (f : E ⟶ G)
      (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U
        (canonicalNabla E U D m) =
      canonicalNabla G U D
        (((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U m)
  pullbackTheta_natural {E G : SchemeObject.IntegrableHiggs T} (f : E ⟶ G)
      (U : X.Opens) (D : Γ(frobeniusPullback F T.tangent, U))
      (m : Γ(pulledBackCarrier F E, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U
        (pullbackTheta E U D m) =
      pullbackTheta G U D
        (((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U m)

namespace GlobalCartierData

variable {T : RestrictedTangentSheaf X p} {F : X ⟶ X}

/-- The Higgs correction `(F⁺θ) ∘ ζ` associated to a global
Frobenius lift. -/
noncomputable def correction (D : GlobalCartierData T F)
    (E : SchemeObject.IntegrableHiggs T) (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End ℤ Γ(pulledBackCarrier F E, U) :=
  (D.pullbackTheta E U).comp (D.zeta U)

@[simp]
lemma correction_apply (D : GlobalCartierData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    D.correction E U v m = D.pullbackTheta E U (D.zeta U v) m := rfl

lemma correction_restrict (D : GlobalCartierData T F)
    (E : SchemeObject.IntegrableHiggs T)
    {U V : X.Opens} (i : U ⟶ V) (v : Γ(T.tangent, V))
    (m : Γ(pulledBackCarrier F E, V)) :
    (pulledBackCarrier F E).presheaf.map i.op (D.correction E V v m) =
      D.correction E U (T.tangent.presheaf.map i.op v)
        ((pulledBackCarrier F E).presheaf.map i.op m) := by
  rw [correction_apply, D.pullbackTheta_restrict, D.zeta_restrict]
  rfl

lemma correction_smul (D : GlobalCartierData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v : Γ(T.tangent, U))
    (a : Γ(X, U)) (m : Γ(pulledBackCarrier F E, U)) :
    D.correction E U v (a • m) = a • D.correction E U v m :=
  D.pullbackTheta_smul E U (D.zeta U v) a m

lemma correction_commutes (D : GlobalCartierData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v w : Γ(T.tangent, U))
    (m : Γ(pulledBackCarrier F E, U)) :
    D.correction E U v (D.correction E U w m) =
      D.correction E U w (D.correction E U v m) :=
  D.pullbackTheta_commutes E U (D.zeta U v) (D.zeta U w) m

lemma correction_natural (D : GlobalCartierData T F)
    {E G : SchemeObject.IntegrableHiggs T} (f : E ⟶ G)
    (U : X.Opens) (v : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U
        (D.correction E U v m) =
      D.correction G U v
        (((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U m) :=
  D.pullbackTheta_natural f U (D.zeta U v) m

end GlobalCartierData

/-- The zero-curvature identity supplied by the divided differential of a
global Frobenius lift after the Higgs correction has been formed.

There is deliberately no nilpotence or `p`-curvature field here: this data
constructs a connection for every integrable Higgs object. -/
structure GlobalDividedFrobeniusData
    (T : RestrictedTangentSheaf X p) (F : X ⟶ X)
    extends GlobalCartierData T F where
  correction_closed (E : SchemeObject.IntegrableHiggs T) (U : X.Opens)
      (D E' : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    toGlobalCartierData.correction E U (T.bracket U D E') m =
      toGlobalCartierData.canonicalNabla E U D
          (toGlobalCartierData.correction E U E' m) -
        toGlobalCartierData.correction E U E'
          (toGlobalCartierData.canonicalNabla E U D m) -
        toGlobalCartierData.canonicalNabla E U E'
          (toGlobalCartierData.correction E U D m) +
        toGlobalCartierData.correction E U D
          (toGlobalCartierData.canonicalNabla E U E' m)

namespace GlobalDividedFrobeniusData

variable {T : RestrictedTangentSheaf X p} {F : X ⟶ X}

/-- The LSZ connection operator `∇ᶜᵃⁿ + (F⁺θ) ∘ ζ`. -/
noncomputable def nabla (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T) (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End ℤ Γ(pulledBackCarrier F E, U) :=
  D.canonicalNabla E U + D.toGlobalCartierData.correction E U

@[simp]
lemma nabla_apply (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v : Γ(T.tangent, U)) (m : Γ(pulledBackCarrier F E, U)) :
    D.nabla E U v m =
      D.canonicalNabla E U v m + D.toGlobalCartierData.correction E U v m := rfl

lemma nabla_restrict (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T)
    {U V : X.Opens} (i : U ⟶ V) (v : Γ(T.tangent, V))
    (m : Γ(pulledBackCarrier F E, V)) :
    (pulledBackCarrier F E).presheaf.map i.op (D.nabla E V v m) =
      D.nabla E U (T.tangent.presheaf.map i.op v)
        ((pulledBackCarrier F E).presheaf.map i.op m) := by
  rw [nabla_apply, map_add, D.canonical_restrict,
    D.toGlobalCartierData.correction_restrict]
  rfl

lemma nabla_leibniz (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v : Γ(T.tangent, U))
    (a : Γ(X, U)) (m : Γ(pulledBackCarrier F E, U)) :
    D.nabla E U v (a • m) =
      a • D.nabla E U v m + T.anchor U v a • m := by
  rw [nabla_apply, D.canonical_leibniz,
    D.toGlobalCartierData.correction_smul, nabla_apply, smul_add]
  abel

lemma nabla_flat (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T)
    (U : X.Opens) (v w : Γ(T.tangent, U))
    (m : Γ(pulledBackCarrier F E, U)) :
    D.nabla E U (T.bracket U v w) m =
      D.nabla E U v (D.nabla E U w m) -
        D.nabla E U w (D.nabla E U v m) := by
  simp only [nabla_apply, map_add]
  rw [D.canonical_flat, D.correction_closed,
    D.toGlobalCartierData.correction_commutes E U v w m]
  abel

lemma nabla_natural (D : GlobalDividedFrobeniusData T F)
    {E G : SchemeObject.IntegrableHiggs T} (f : E ⟶ G)
    (U : X.Opens) (v : Γ(T.tangent, U))
    (m : Γ(pulledBackCarrier F E, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U
        (D.nabla E U v m) =
      D.nabla G U v
        (((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U m) := by
  rw [nabla_apply, map_add, D.canonical_natural f U v m,
    D.toGlobalCartierData.correction_natural f U v m, nabla_apply]

/-- The integrable connection produced by the global LSZ formula. -/
noncomputable def connection (D : GlobalDividedFrobeniusData T F)
    (E : SchemeObject.IntegrableHiggs T) : SchemeObject.IntegrableConnection T where
  carrier := pulledBackCarrier F E
  carrier_quasicoherent :=
    D.pullback_quasicoherent E.carrier E.carrier_quasicoherent
  nabla := D.nabla E
  nabla_restrict := D.nabla_restrict E
  leibniz := D.nabla_leibniz E
  flat := D.nabla_flat E

/-- Morphism part of the global LSZ transform: pull back the Higgs morphism
by Frobenius. -/
noncomputable def map (D : GlobalDividedFrobeniusData T F)
    {E G : SchemeObject.IntegrableHiggs T} (f : E ⟶ G) :
    D.connection E ⟶ D.connection G where
  hom := (AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom
  horizontal U v m := by
    change ((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U
        (D.nabla E U v m) =
      D.nabla G U v
        (((AlgebraicGeometry.Scheme.Modules.pullback F).map f.hom).app U m)
    exact D.nabla_natural f U v m

end GlobalDividedFrobeniusData

/-- The unrestricted functor defined by the global LSZ formula for a
supplied divided Frobenius datum. -/
noncomputable def globalLSZFunctorOfDividedFrobenius
    {T : RestrictedTangentSheaf X p} {F : X ⟶ X}
    (D : GlobalDividedFrobeniusData T F) :
    SchemeObject.IntegrableHiggs T ⥤ SchemeObject.IntegrableConnection T where
  obj := D.connection
  map := D.map
  map_id E := by
    apply SchemeObject.ConnectionHom.ext
    exact (AlgebraicGeometry.Scheme.Modules.pullback F).map_id E.carrier
  map_comp f g := by
    apply SchemeObject.ConnectionHom.ext
    exact (AlgebraicGeometry.Scheme.Modules.pullback F).map_comp f.hom g.hom

end Global

namespace GlobalFrobeniusLift

open SchemeObject Global

variable {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {X : AlgebraicGeometry.Scheme.{u}}
variable {L : W₂Lift (p := p) (k := k) X}

/-- The differential package canonically expected from a fixed global
Frobenius lifting.  Its fields spell out `d F̃/[p]` and the identities used
in the LSZ proof; it does not contain a functor or a nilpotence assumption. -/
abbrev DividedDifferentialData
    (Phi : LSZ.GlobalFrobeniusLift X L) (T : RestrictedTangentSheaf X p) :=
  GlobalDividedFrobeniusData T Phi.frobenius

/-- Given one `W₂(k)`-lifting, one global Frobenius lifting, and its divided
differential, the unrestricted LSZ functor

`(E,θ) ↦ (Phi.frobenius⁺ E, d + (Phi.frobenius⁺θ)∘dPhi/[p])`.

No word-nilpotence hypothesis occurs in its source or target. -/
noncomputable def globalLSZFunctor
    (Phi : LSZ.GlobalFrobeniusLift X L) (T : RestrictedTangentSheaf X p)
    (D : Phi.DividedDifferentialData T) :
    SchemeObject.IntegrableHiggs T ⥤ SchemeObject.IntegrableConnection T :=
  globalLSZFunctorOfDividedFrobenius D

end GlobalFrobeniusLift

end LSZ
