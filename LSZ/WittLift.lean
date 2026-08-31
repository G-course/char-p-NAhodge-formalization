import LSZ.SchemeObjects
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.WittVector.Truncated

/-!
# Length-two Witt liftings used by the LSZ construction

This file contains only the geometric input.  In particular, it does not
postulate an LSZ functor.  The functor is constructed in `LSZ.GlobalFunctor`
from the divided differential of a Frobenius lifting.

We follow the convention requested for this project: after using perfection
of the ground field to choose the usual identification, Frobenius is an
endomorphism of the same special-fibre scheme `X`; no second scheme named
`X'` occurs in the definitions.
-/

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace LSZ

universe u

/-- The ring `W₂(k)` of `p`-typical Witt vectors of length two. -/
abbrev W₂ (p : ℕ) (k : Type u) := TruncatedWittVector p 2 k

namespace TruncatedWittVector

variable {p n : ℕ} {R S : Type u}
variable [CommRing R] [CommRing S] [Fact p.Prime]

/-- Functoriality of truncated Witt vectors.  Mathlib currently exposes
`WittVector.map` and truncation separately; this is their induced map on a
fixed truncation length. -/
noncomputable def map (f : R →+* S) :
    TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n)
    TruncatedWittVector.out TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), by
      intro x hx
      rw [WittVector.mem_ker_truncate] at hx
      change WittVector.map f x ∈ RingHom.ker (WittVector.truncate n)
      rw [WittVector.mem_ker_truncate]
      intro i hi
      simp only [WittVector.map_coeff, hx i hi, map_zero]⟩

@[simp]
lemma map_wittVector_truncate (f : R →+* S) (x : WittVector p R) :
    map (n := n) f (WittVector.truncate n x) =
      WittVector.truncate n (WittVector.map f x) := by
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]
lemma coeff_map (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map (p := p) f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n R x
  simp

@[simp]
lemma map_id : map (p := p) (n := n) (RingHom.id R) =
    RingHom.id (TruncatedWittVector p n R) := by
  ext x i
  simp

@[simp]
lemma map_comp (f : R →+* S) {T : Type u} [CommRing T] (g : S →+* T) :
    (map (p := p) (n := n) g).comp (map (p := p) f) =
      map (p := p) (g.comp f) := by
  ext x i
  simp

end TruncatedWittVector

section WittBase

variable (p : ℕ) (k : Type u)
variable [Field k] [CharP k p] [Fact p.Prime]

/-- Reduction modulo `p`, `W₂(k) → k`, given by the zeroth Witt
coordinate. -/
noncomputable def w₂Reduction : W₂ p k →+* k :=
  RingHom.liftOfRightInverse (WittVector.truncate 2)
    TruncatedWittVector.out TruncatedWittVector.truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      rw [WittVector.mem_ker_truncate] at hx
      exact hx 0 (by omega)⟩

omit [CharP k p] in
@[simp]
lemma w₂Reduction_wittVector_truncate (x : WittVector p k) :
    w₂Reduction p k (WittVector.truncate 2 x) = x.coeff 0 := by
  exact RingHom.liftOfRightInverse_comp_apply _ _
    _ _ _

omit [CharP k p] in
@[simp]
lemma w₂Reduction_apply (x : W₂ p k) : w₂Reduction p k x = x.coeff ⟨0, by omega⟩ := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) 2 k x
  simp

/-- The canonical Witt Frobenius on `W₂(k)`. -/
noncomputable def w₂Frobenius : W₂ p k →+* W₂ p k :=
  TruncatedWittVector.map (frobenius k p)

@[simp]
lemma w₂Reduction_frobenius :
    (w₂Reduction p k).comp (w₂Frobenius p k) =
      (frobenius k p).comp (w₂Reduction p k) := by
  ext x
  simp [w₂Frobenius, frobenius_def]

/-- The morphism `Spec k ⟶ Spec W₂(k)` defining the special fibre. -/
noncomputable def specialFiberPoint :
    AlgebraicGeometry.Spec (.of k) ⟶
      AlgebraicGeometry.Spec (.of (W₂ p k)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (w₂Reduction p k))

/-- The Frobenius endomorphism of `Spec W₂(k)`. -/
noncomputable def w₂FrobeniusSpec :
    AlgebraicGeometry.Spec (.of (W₂ p k)) ⟶
      AlgebraicGeometry.Spec (.of (W₂ p k)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (w₂Frobenius p k))

/-- The Frobenius endomorphism of `Spec k`. -/
noncomputable def fieldFrobeniusSpec :
    AlgebraicGeometry.Spec (.of k) ⟶
      AlgebraicGeometry.Spec (.of k) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (frobenius k p))

lemma specialFiberPoint_frobenius :
    specialFiberPoint p k ≫ w₂FrobeniusSpec p k =
      fieldFrobeniusSpec p k ≫ specialFiberPoint p k := by
  rw [specialFiberPoint, w₂FrobeniusSpec, fieldFrobeniusSpec,
    ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1

end WittBase

section Lift

variable {p : ℕ} {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable (X : AlgebraicGeometry.Scheme.{u})

/-- A smooth `W₂(k)`-lifting of the `k`-scheme `X`.

The special fibre is represented by the actual scheme-theoretic pullback,
and `specialFiberIso` identifies it with `X`.  The final equation says that
this identification respects the given structure morphism of `X` over
`Spec k`. -/
structure W₂Lift where
  structureMap : X ⟶ AlgebraicGeometry.Spec (.of k)
  smooth : AlgebraicGeometry.Smooth structureMap
  lift : AlgebraicGeometry.Scheme.{u}
  liftStructureMap : lift ⟶ AlgebraicGeometry.Spec (.of (W₂ p k))
  liftSmooth : AlgebraicGeometry.Smooth liftStructureMap
  specialFiberIso :
    pullback liftStructureMap (specialFiberPoint p k) ≅ X
  specialFiberIso_over :
    specialFiberIso.hom ≫ structureMap = pullback.snd _ _

namespace W₂Lift

variable {X}

/-- The special fibre of a fixed `W₂(k)`-lifting. -/
noncomputable abbrev specialFiber (L : W₂Lift (p := p) (k := k) X) :
    AlgebraicGeometry.Scheme.{u} :=
  pullback L.liftStructureMap (specialFiberPoint p k)

end W₂Lift

/-- A global Frobenius lifting on a fixed `W₂(k)`-lifting.

`specialFiberMap` is recorded explicitly together with its two projection
identities.  These equations state that it is the reduction of `liftFrob`.
The last field states that, after identifying the special fibre with `X`,
the resulting endomorphism is the chosen absolute Frobenius on `X`.

Keeping `frobenius : X ⟶ X` as data avoids introducing a second base
scheme.  In applications it is instantiated by absolute Frobenius (or by
the relative Frobenius after the standard perfect-field identification).
-/
structure GlobalFrobeniusLift (L : W₂Lift (p := p) (k := k) X) where
  frobenius : X ⟶ X
  liftFrob : L.lift ⟶ L.lift
  liftFrob_over :
    liftFrob ≫ L.liftStructureMap =
      L.liftStructureMap ≫ w₂FrobeniusSpec p k
  specialFiberMap : L.specialFiber ⟶ L.specialFiber
  specialFiberMap_fst :
    specialFiberMap ≫ pullback.fst _ _ = pullback.fst _ _ ≫ liftFrob
  specialFiberMap_snd :
    specialFiberMap ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ fieldFrobeniusSpec p k
  reduction_eq :
    L.specialFiberIso.inv ≫ specialFiberMap ≫ L.specialFiberIso.hom = frobenius

end Lift

end LSZ
