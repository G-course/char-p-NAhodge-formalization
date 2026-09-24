import LSZ.GeometricWittLift
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# The topology and section maps of a geometric Frobenius lift

For a perfect field `k`, the closed point
`Spec k ⟶ Spec W₂(k)` is surjective on prime spectra: its defining ideal
is nilpotent.  Consequently the special-fibre projection of any
`W₂(k)`-scheme is surjective.

If a lifted endomorphism reduces to absolute Frobenius, this surjectivity
forces the lifted endomorphism to be the identity on the underlying
topological space.  It therefore acts on the ring of sections of every
*same* open subset.  The final definitions package these same-open maps as
an endomorphism of the structure presheaf; this is the input needed for the
geometric divided-Frobenius differential.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

noncomputable section

variable (p : ℕ) (k : Type u)
variable [Field k] [CharP k p] [Fact p.Prime] [PerfectField k]

/-- The residue-field point of `Spec W₂(k)` is surjective on points.

The proof uses surjectivity of reduction and nilpotence of its kernel;
over the fixed perfect field the latter follows from `p² = 0`. -/
lemma specialFiberPoint_surjective :
    Function.Surjective (specialFiberPoint p k) := by
  rw [specialFiberPoint]
  change Function.Surjective (PrimeSpectrum.comap (w₂Reduction p k))
  apply (PrimeSpectrum.isHomeomorph_comap (w₂Reduction p k) _ _).surjective
  · intro x
    obtain ⟨y, hy⟩ := w₂Reduction_surjective p k x
    refine ⟨1, Nat.zero_lt_one, y, ?_⟩
    simpa using hy
  · intro x hx
    rw [mem_nilradical]
    change w₂Reduction p k x = 0 at hx
    obtain ⟨y, rfl⟩ := (w₂Reduction_eq_zero_iff_exists_mul_p p k x).mp hx
    refine ⟨2, ?_⟩
    rw [mul_pow, w₂_p_sq, mul_zero]

/-- Bundled form of `specialFiberPoint_surjective`, so stability of
surjectivity under base change can be used by typeclass inference. -/
instance specialFiberPointSurjective :
    AlgebraicGeometry.Surjective (specialFiberPoint p k) where
  surj := specialFiberPoint_surjective p k

/-- The residue-field point is a closed immersion. -/
instance specialFiberPointClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion (specialFiberPoint p k) := by
  rw [specialFiberPoint]
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (w₂Reduction_surjective p k)

namespace SmoothScheme.W₂Lift

variable {p : ℕ} {k : Type u}
variable [Field k] [CharP k p] [Fact p.Prime] [PerfectField k]
variable {X : LSZ.SmoothScheme k}

/-- Projection from the special fibre to its `W₂(k)`-lift. -/
def specialFiberProjection (L : X.W₂Lift (p := p)) :
    L.specialFiber ⟶ L.lift :=
  pullback.fst L.structureMap (LSZ.specialFiberPoint p k)

instance (L : X.W₂Lift (p := p)) :
    AlgebraicGeometry.IsClosedImmersion L.specialFiberProjection := by
  dsimp [specialFiberProjection]
  infer_instance

instance (L : X.W₂Lift (p := p)) :
    AlgebraicGeometry.Surjective L.specialFiberProjection := by
  dsimp [specialFiberProjection]
  infer_instance

/-- A special fibre and its length-two Witt lift have the same underlying
topological space. -/
noncomputable def specialFiberHomeomorph (L : X.W₂Lift (p := p)) :
    L.specialFiber ≃ₜ L.lift :=
  L.specialFiberProjection.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    L.specialFiberProjection.surjective

@[simp]
lemma specialFiberHomeomorph_apply (L : X.W₂Lift (p := p))
    (x : L.specialFiber) :
    L.specialFiberHomeomorph x = L.specialFiberProjection x := rfl

/-- The underlying space of a lift is canonically homeomorphic to the
fixed special fibre `X`. -/
noncomputable def liftToSpecialFiberSchemeHomeomorph
    (L : X.W₂Lift (p := p)) : L.lift ≃ₜ X.scheme :=
  L.specialFiberHomeomorph.symm.trans
    (AlgebraicGeometry.Scheme.homeoOfIso L.specialFiberIso)

/-- The open of `X` obtained by reducing an affine open of the lift. -/
def affineOpen (L : X.W₂Lift (p := p)) (V : L.lift.affineOpens) :
    X.scheme.Opens :=
  L.specialFiberIso.inv ⁻¹ᵁ
    (L.specialFiberProjection ⁻¹ᵁ V.1)

/-- Reduction of an affine open of the lift is affine. -/
lemma affineOpen_isAffine (L : X.W₂Lift (p := p))
    (V : L.lift.affineOpens) :
    AlgebraicGeometry.IsAffineOpen (L.affineOpen V) := by
  exact (V.2.preimage L.specialFiberProjection).preimage_of_isIso
    L.specialFiberIso.inv

/-- Affine opens of the lift reduce to an affine open cover of `X`. -/
lemma affineOpen_cover (L : X.W₂Lift (p := p)) :
    IsOpenCover (fun V : L.lift.affineOpens ↦ L.affineOpen V) := by
  exact TopologicalSpace.IsOpenCover.comap
    (AlgebraicGeometry.iSup_affineOpens_eq_top L.lift)
    (L.specialFiberIso.inv ≫ L.specialFiberProjection).base.hom

end SmoothScheme.W₂Lift

namespace SmoothScheme.FrobeniusLift

variable {p : ℕ} {k : Type u}
variable [Field k] [CharP k p] [Fact p.Prime]
variable {X : LSZ.SmoothScheme k} {L : X.W₂Lift (p := p)}

/-- Transporting the special-fibre reduction through its fixed
identification with `X` gives the absolute Frobenius square. -/
lemma specialFiberMap_comp_specialFiberIso
    (Phi : X.FrobeniusLift L) :
    Phi.specialFiberMap ≫ L.specialFiberIso.hom =
      L.specialFiberIso.hom ≫
        AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X.scheme := by
  rw [← cancel_epi L.specialFiberIso.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    Phi.reduction_eq_absoluteFrobenius

/-- The reduced endomorphism fixes every point of the special fibre. -/
lemma specialFiberMap_apply (Phi : X.FrobeniusLift L)
    (x : L.specialFiber) :
    Phi.specialFiberMap x = x := by
  apply (ConcreteCategory.bijective_of_isIso L.specialFiberIso.hom.base).injective
  have h := congrArg (fun f ↦ f x)
    (specialFiberMap_comp_specialFiberIso Phi)
  change L.specialFiberIso.hom (Phi.specialFiberMap x) =
    AlgebraicGeometry.Scheme.absoluteFrobenius (p := p) X.scheme
      (L.specialFiberIso.hom x) at h
  rw [AlgebraicGeometry.Scheme.absoluteFrobenius_apply] at h
  exact h

variable [PerfectField k]

/-- A genuine lifted Frobenius is the identity on the underlying
topological space of the `W₂(k)`-lift. -/
lemma liftFrob_apply (Phi : X.FrobeniusLift L) (y : L.lift) :
    Phi.liftFrob y = y := by
  obtain ⟨x, rfl⟩ :=
    (pullback.fst L.structureMap (LSZ.specialFiberPoint p k)).surjective y
  have h := congrArg (fun f ↦ f x) Phi.specialFiberMap_fst
  change (pullback.fst L.structureMap (LSZ.specialFiberPoint p k))
      (Phi.specialFiberMap x) =
    Phi.liftFrob
      ((pullback.fst L.structureMap (LSZ.specialFiberPoint p k)) x) at h
  rw [specialFiberMap_apply Phi x] at h
  exact h.symm

/-- Equality of underlying continuous maps corresponding to
`liftFrob_apply`. -/
lemma liftFrob_base (Phi : X.FrobeniusLift L) :
    Phi.liftFrob.base = 𝟙 (L.lift : TopCat) := by
  ext y
  exact liftFrob_apply Phi y

/-- Every open subset of the lift is invariant under the lifted
Frobenius. -/
@[simp]
lemma liftFrob_preimage (Phi : X.FrobeniusLift L) (U : L.lift.Opens) :
    Phi.liftFrob ⁻¹ᵁ U = U := by
  ext y
  change Phi.liftFrob y ∈ U ↔ y ∈ U
  rw [liftFrob_apply Phi y]

/-- The endomorphism induced by a lifted Frobenius on one fixed open
subset of the lift. -/
def app (Phi : X.FrobeniusLift L) (U : L.lift.Opens) :
    Γ(L.lift, U) ⟶ Γ(L.lift, U) :=
  Phi.liftFrob.appLE U U (by rw [Phi.liftFrob_preimage U])

/-- The same-open maps commute with restriction. -/
lemma app_naturality (Phi : X.FrobeniusLift L)
    {U V : L.lift.Opens} (h : V ≤ U) :
    Phi.app U ≫ L.lift.presheaf.map (homOfLE h).op =
      L.lift.presheaf.map (homOfLE h).op ≫ Phi.app V := by
  rw [app, AlgebraicGeometry.Scheme.Hom.appLE_map]
  rw [app, AlgebraicGeometry.Scheme.Hom.map_appLE]

/-- The same-open section maps form an endomorphism of the structure
presheaf of the lift. -/
def presheafEnd (Phi : X.FrobeniusLift L) :
    L.lift.presheaf ⟶ L.lift.presheaf where
  app U := Phi.app U.unop
  naturality {U V} i := by
    have hi : i = (homOfLE i.unop.le).op := Subsingleton.elim _ _
    rw [hi]
    exact (Phi.app_naturality i.unop.le).symm

@[simp]
lemma presheafEnd_app (Phi : X.FrobeniusLift L) (U : L.lift.Opens) :
    Phi.presheafEnd.app (.op U) = Phi.app U := rfl

/-- The coordinate ring of an affine open in the lifted scheme. -/
abbrev affineRing (V : L.lift.affineOpens) := Γ(L.lift, V.1)

/-- The `W₂(k)`-algebra structure on the coordinate ring of an affine
open of the lift, obtained from the structure morphism. -/
def affineAlgebraMap (V : L.lift.affineOpens) :
    W₂ p k →+* affineRing V :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso (.of (W₂ p k))).inv ≫
    L.structureMap.appLE ⊤ V.1 le_top).hom

instance affineAlgebra (V : L.lift.affineOpens) :
    Algebra (W₂ p k) (affineRing V) :=
  (affineAlgebraMap V).toAlgebra

/-- Coordinate rings of affine opens in a smooth `W₂(k)`-scheme are
smooth `W₂(k)`-algebras. -/
instance affineSmooth (V : L.lift.affineOpens) :
    Algebra.Smooth (W₂ p k) (affineRing V) := by
  rw [← RingHom.smooth_algebraMap]
  change (affineAlgebraMap V).Smooth
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso
        (AlgebraicGeometry.Scheme.ΓSpecIso (.of (W₂ p k))).inv))
    (L.structureMap.smooth_appLE
      (AlgebraicGeometry.isAffineOpen_top _) V.2 le_top)

/-- The ring endomorphism induced by the geometric Frobenius lift on an
invariant affine open. -/
def affineMap (Phi : X.FrobeniusLift L)
    (V : L.lift.affineOpens) : affineRing V →+* affineRing V :=
  (Phi.app V.1).hom

/-- On an affine open, the structural section map followed by the lifted
Frobenius equals Witt Frobenius followed by the structural section map. -/
lemma structureMap_appLE_comp_affineMap (Phi : X.FrobeniusLift L)
    (V : L.lift.affineOpens) :
    L.structureMap.appLE ⊤ V.1 le_top ≫ Phi.app V.1 =
      (LSZ.w₂FrobeniusSpec p k).appTop ≫
        L.structureMap.appLE ⊤ V.1 le_top := by
  calc
    _ = (Phi.liftFrob ≫ L.structureMap).appLE ⊤ V.1 _ := by
      simpa only [FrobeniusLift.app] using
        (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
          Phi.liftFrob L.structureMap ⊤ V.1 V.1
          (by exact le_top) (by rw [Phi.liftFrob_preimage V.1]))
    _ = (L.structureMap ≫ LSZ.w₂FrobeniusSpec p k).appLE ⊤ V.1 _ := by
      rw [Phi.liftFrob_over]
    _ = (LSZ.w₂FrobeniusSpec p k).appTop ≫
        L.structureMap.appLE ⊤ V.1 le_top := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_appLE]
      simp

/-- The endomorphism on every affine coordinate ring is semilinear for
Witt Frobenius. -/
lemma affineMap_base (Phi : X.FrobeniusLift L)
    (V : L.lift.affineOpens) (r : W₂ p k) :
    affineMap Phi V (algebraMap (W₂ p k) (affineRing V) r) =
      algebraMap (W₂ p k) (affineRing V) (w₂Frobenius p k r) := by
  change (Phi.app V.1).hom
      (((AlgebraicGeometry.Scheme.ΓSpecIso (.of (W₂ p k))).inv ≫
        L.structureMap.appLE ⊤ V.1 le_top).hom r) = _
  rw [← CommRingCat.comp_apply, Category.assoc,
    structureMap_appLE_comp_affineMap Phi V]
  rw [LSZ.w₂FrobeniusSpec]
  rw [← Category.assoc, ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
  rfl

end SmoothScheme.FrobeniusLift

end

end LSZ
