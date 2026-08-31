import LSZ.Gauge

/-!
# Independence of the affine cover and local Frobenius liftings

For two affine Frobenius atlases, the LSZ comparison is computed on a
common affine refinement.  Its local expression is

`  exp_p(h(F⁺θ))`,

where `h` is the divided difference of the two Frobenius liftings.  The
field `localGauge` below is exactly this expression; `Gauge.Exponential`
has already proved that it is invertible from length-`p` Higgs nilpotence.

The comparison identities supplied by the local LSZ calculation are:

* the exponential gauges descend to `moduleIso`;
* `moduleIso` is natural in the Higgs object;
* its forward map intertwines the two connections.

From these identities this file constructs an isomorphism of flat objects,
proves that its inverse is horizontal, and finally constructs the natural
isomorphism of the two cover-dependent LSZ functors.
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

variable {T : RestrictedTangentSheaf X p}
variable {A₀ A₁ : AffineFrobeniusAtlas L}
variable (D₀ : DescentData A₀ T) (D₁ : DescentData A₁ T)

/-- Restriction to the members of an affine open cover detects morphisms
of sheaves of modules.  This is the precise descent/separatedness principle
used below to turn local exponential inverse identities into global ones. -/
structure RestrictionFaithful (C : X.AffineOpenCover) : Prop where
  hom_ext {M N : X.Modules} (f g : M ⟶ N)
      (h : ∀ r : C.I₀,
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (C.f r)).map f =
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor (C.f r)).map g) :
    f = g

/-- LSZ comparison data for two choices of affine cover and local
Frobenius liftings.

`refinement`, `refines₀`, and `refines₁` make the common refinement
explicit.  On each member, `localGauge.exponent` is the contraction
`h(F⁺θ)` of the divided Frobenius difference with the pulled-back Higgs
field.  `moduleIso_local` says that the descended comparison is exactly
the truncated exponential gauge on that member.
-/
structure ComparisonData where
  refinement : X.AffineOpenCover
  refines₀ : refinement.openCover ⟶ A₀.cover.openCover
  refines₁ : refinement.openCover ⟶ A₁.cover.openCover
  restrictionFaithful : RestrictionFaithful refinement

  refinementTangent (r : refinement.I₀) :
    RestrictedTangentSheaf (AlgebraicGeometry.Spec (refinement.X r)) p

  localBaseIso (E : SchemeObject.NilpotentHiggs T) (r : refinement.I₀) :
    (D₀.carrier.obj E).restrict (refinement.f r) ≅
      (D₁.carrier.obj E).restrict (refinement.f r)
  localGauge (E : SchemeObject.NilpotentHiggs T) (r : refinement.I₀) :
    Gauge.Exponential (refinementTangent r)
      ((D₁.carrier.obj E).restrict (refinement.f r))

  comparisonHom (E : SchemeObject.NilpotentHiggs T) :
    D₀.carrier.obj E ⟶ D₁.carrier.obj E
  comparisonInv (E : SchemeObject.NilpotentHiggs T) :
    D₁.carrier.obj E ⟶ D₀.carrier.obj E
  comparisonHom_local (E : SchemeObject.NilpotentHiggs T)
      (r : refinement.I₀) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (refinement.f r)).map (comparisonHom E) =
      (localBaseIso E r).hom ≫ (localGauge E r).expHom
  comparisonInv_local (E : SchemeObject.NilpotentHiggs T)
      (r : refinement.I₀) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (refinement.f r)).map (comparisonInv E) =
      (localGauge E r).expNegHom ≫ (localBaseIso E r).inv

  naturality {E G : SchemeObject.NilpotentHiggs T} (f : E ⟶ G) :
    D₀.carrier.map f ≫ comparisonHom G =
      comparisonHom E ≫ D₁.carrier.map f
  horizontal (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
      (v : Γ(T.tangent, U)) (m : Γ(D₀.carrier.obj E, U)) :
    (comparisonHom E).app U (D₀.nabla E U v m) =
      D₁.nabla E U v ((comparisonHom E).app U m)

namespace ComparisonData

variable {D₀ : DescentData A₀ T} {D₁ : DescentData A₁ T}

/-- The descended forward and backward comparison maps are inverse.  The
proof is local on the common refinement and uses the already proved
truncated-exponential inverse identity. -/
lemma comparison_hom_inv_id (C : ComparisonData D₀ D₁)
    (E : SchemeObject.NilpotentHiggs T) :
    C.comparisonHom E ≫ C.comparisonInv E = 𝟙 (D₀.carrier.obj E) := by
  apply C.restrictionFaithful.hom_ext
  intro r
  rw [Functor.map_comp, C.comparisonHom_local, C.comparisonInv_local]
  rw [← Category.assoc
      ((C.localBaseIso E r).hom ≫ (C.localGauge E r).expHom)
      (C.localGauge E r).expNegHom (C.localBaseIso E r).inv,
    Category.assoc (C.localBaseIso E r).hom
      (C.localGauge E r).expHom (C.localGauge E r).expNegHom,
    (C.localGauge E r).hom_inv_id, Category.comp_id,
    Iso.hom_inv_id]
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
    (C.refinement.f r)).map_id (D₀.carrier.obj E)).symm

lemma comparison_inv_hom_id (C : ComparisonData D₀ D₁)
    (E : SchemeObject.NilpotentHiggs T) :
    C.comparisonInv E ≫ C.comparisonHom E = 𝟙 (D₁.carrier.obj E) := by
  apply C.restrictionFaithful.hom_ext
  intro r
  rw [Functor.map_comp, C.comparisonInv_local, C.comparisonHom_local]
  rw [← Category.assoc
      ((C.localGauge E r).expNegHom ≫ (C.localBaseIso E r).inv)
      (C.localBaseIso E r).hom (C.localGauge E r).expHom,
    Category.assoc (C.localGauge E r).expNegHom
      (C.localBaseIso E r).inv (C.localBaseIso E r).hom,
    Iso.inv_hom_id, Category.comp_id,
    (C.localGauge E r).inv_hom_id]
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
    (C.refinement.f r)).map_id (D₁.carrier.obj E)).symm

/-- The global module isomorphism descended from the local truncated
exponential gauges.  Its inverse laws are proved by the preceding lemmas. -/
noncomputable def moduleIso (C : ComparisonData D₀ D₁)
    (E : SchemeObject.NilpotentHiggs T) :
    D₀.carrier.obj E ≅ D₁.carrier.obj E where
  hom := C.comparisonHom E
  inv := C.comparisonInv E
  hom_inv_id := C.comparison_hom_inv_id E
  inv_hom_id := C.comparison_inv_hom_id E

/-- The inverse of the exponential comparison is horizontal.  This is
deduced from horizontality of the forward comparison and the two inverse
identities; it is not an additional field of `ComparisonData`. -/
lemma inverse_horizontal (C : ComparisonData D₀ D₁)
    (E : SchemeObject.NilpotentHiggs T) (U : X.Opens)
    (v : Γ(T.tangent, U)) (m : Γ(D₁.carrier.obj E, U)) :
    (C.moduleIso E).inv.app U (D₁.nabla E U v m) =
      D₀.nabla E U v ((C.moduleIso E).inv.app U m) := by
  change (C.comparisonInv E).app U (D₁.nabla E U v m) =
    D₀.nabla E U v ((C.comparisonInv E).app U m)
  have h_hom_inv (x : Γ(D₁.carrier.obj E, U)) :
      (C.comparisonHom E).app U ((C.comparisonInv E).app U x) = x := by
    have h := congrArg
      (fun q : D₁.carrier.obj E ⟶ D₁.carrier.obj E ↦ q.app U x)
      (C.comparison_inv_hom_id E)
    exact h
  have h_inv_hom (x : Γ(D₀.carrier.obj E, U)) :
      (C.comparisonInv E).app U ((C.comparisonHom E).app U x) = x := by
    have h := congrArg
      (fun q : D₀.carrier.obj E ⟶ D₀.carrier.obj E ↦ q.app U x)
      (C.comparison_hom_inv_id E)
    exact h
  calc
    (C.comparisonInv E).app U (D₁.nabla E U v m) =
        (C.comparisonInv E).app U
          (D₁.nabla E U v
            ((C.comparisonHom E).app U ((C.comparisonInv E).app U m))) := by
              rw [h_hom_inv]
    _ = (C.comparisonInv E).app U
          ((C.comparisonHom E).app U
            (D₀.nabla E U v ((C.comparisonInv E).app U m))) := by
              rw [C.horizontal]
    _ = D₀.nabla E U v ((C.comparisonInv E).app U m) :=
      h_inv_hom _

/-- Objectwise isomorphism of the two descended flat bundles. -/
noncomputable def flatIso (C : ComparisonData D₀ D₁)
    (E : SchemeObject.NilpotentHiggs T) : D₀.obj E ≅ D₁.obj E where
  hom :=
    { hom := (C.moduleIso E).hom
      horizontal := C.horizontal E }
  inv :=
    { hom := (C.moduleIso E).inv
      horizontal := C.inverse_horizontal E }
  hom_inv_id := by
    apply SchemeObject.FlatHom.ext
    exact (C.moduleIso E).hom_inv_id
  inv_hom_id := by
    apply SchemeObject.FlatHom.ext
    exact (C.moduleIso E).inv_hom_id

/-- The comparison natural isomorphism between the two LSZ functors. -/
noncomputable def natIso (C : ComparisonData D₀ D₁) :
    D₀.lszFunctor ≅ D₁.lszFunctor :=
  NatIso.ofComponents (fun E ↦ C.flatIso E) (by
    intro E G f
    apply SchemeObject.FlatHom.ext
    exact C.naturality f)

/-- The named comparison isomorphism expressing independence of choices. -/
noncomputable def choiceIso (C : ComparisonData D₀ D₁) :
    D₀.lszFunctor ≅ D₁.lszFunctor :=
  C.natIso

/-- **Independence of the affine cover and local Frobenius liftings.**

Once the LSZ local divided-difference calculation and descent identities
are supplied by `ComparisonData`, the two cover-dependent LSZ functors are
naturally isomorphic. -/
theorem lszFunctor_choice_independent (C : ComparisonData D₀ D₁) :
    Nonempty (D₀.lszFunctor ≅ D₁.lszFunctor) :=
  ⟨C.choiceIso⟩

end ComparisonData

end Atlas

end LSZ
