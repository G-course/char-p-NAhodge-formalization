import LSZ.VectorFields
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Absolute Frobenius of a scheme in characteristic `p`

This file constructs absolute Frobenius from the characteristic of the
scheme itself.  The construction does not require the scheme to be smooth,
nor does it obtain the characteristic from a chosen ground field.  A smooth
scheme over a characteristic-`p` field is supplied only as a later instance
of the intrinsic characteristic condition.

The topological map is the identity and the map on the structure sheaf sends
a section `a` to `a ^ p`.  Module pullback is deliberately not reconstructed
as a presheaf here: later files use mathlib's `Scheme.Modules.pullback`.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace LSZ

universe u u₁ u₂

noncomputable section

section Ring

variable (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]

/-- The `p`-power endomorphism of a commutative ring in which `p` vanishes.

The hypothesis is weaker than a `CharP A p` instance and therefore also
covers the zero ring of sections on an empty open subset. -/
def ringFrobenius (hchar : (p : A) = 0) : A →+* A where
  toFun a := a ^ p
  map_one' := one_pow p
  map_mul' a b := mul_pow a b p
  map_zero' := zero_pow ((Fact.out : Nat.Prime p).ne_zero)
  map_add' a b := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := A) (p := p)
      (Fact.out : Nat.Prime p) a b
    rw [hr]
    simp [hchar]

@[simp]
lemma ringFrobenius_apply (hchar : (p : A) = 0) (a : A) :
    ringFrobenius A p hchar a = a ^ p := rfl

end Ring

section Algebra

variable (k : Type u₁) (A : Type u₂) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [CharP k p] [Fact p.Prime]

/-- The `p`-power Frobenius on a `k`-algebra.  This compatibility entry point
is used by the affine canonical-connection construction; absolute Frobenius
of a scheme below does not depend on it. -/
def algebraFrobenius : A →+* A :=
  ringFrobenius A p (by
    calc
      (p : A) = algebraMap k A (p : k) :=
        (map_natCast (algebraMap k A) p).symm
      _ = algebraMap k A 0 :=
        congrArg (algebraMap k A) (CharP.cast_eq_zero k p)
      _ = 0 := map_zero (algebraMap k A))

@[simp]
lemma algebraFrobenius_apply (a : A) :
    algebraFrobenius k A p a = a ^ p := rfl

end Algebra

/-- An intrinsic characteristic-`p` condition on a scheme.

For prime `p`, requiring `p = 0` in global sections is equivalent to the
structure morphism factoring through `Spec (ZMod p)`.  Unlike an exact
`CharP` instance, this formulation includes the empty scheme and its zero
ring of sections. -/
class IsCharacteristicP (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) : Prop where
  cast_eq_zero_top : (p : Γ(X, ⊤)) = 0

namespace IsCharacteristicP

variable {p : ℕ} {X : AlgebraicGeometry.Scheme.{u}} [IsCharacteristicP X p]

/-- If `p` vanishes globally, it vanishes in the ring of sections of every
open subset. -/
lemma cast_eq_zero (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  let ρ : Γ(X, ⊤) ⟶ Γ(X, U) :=
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  have h := congrArg ρ.hom
    (IsCharacteristicP.cast_eq_zero_top (X := X) (p := p))
  simpa using h

end IsCharacteristicP

namespace SmoothScheme

variable {p : ℕ} {k : Type u₁} [Field k] [CharP k p] [Fact p.Prime]

/-- A scheme over a characteristic-`p` field satisfies the intrinsic
characteristic condition.  This is an instance of the generic definition,
not part of the definition of absolute Frobenius. -/
instance (X : SmoothScheme k) : IsCharacteristicP X.scheme p where
  cast_eq_zero_top := by
    calc
      (p : Γ(X.scheme, ⊤)) = algebraMap k Γ(X.scheme, ⊤) (p : k) :=
        (map_natCast (algebraMap k Γ(X.scheme, ⊤)) p).symm
      _ = algebraMap k Γ(X.scheme, ⊤) 0 :=
        congrArg (algebraMap k Γ(X.scheme, ⊤)) (CharP.cast_eq_zero k p)
      _ = 0 := map_zero (algebraMap k Γ(X.scheme, ⊤))

end SmoothScheme

end

end LSZ

namespace AlgebraicGeometry.Scheme

noncomputable section

open LSZ

variable {p : ℕ} [Fact p.Prime]
variable (X : AlgebraicGeometry.Scheme.{u}) [LSZ.IsCharacteristicP X p]

/-- The `p`-power endomorphism of the structure presheaf of an intrinsic
characteristic-`p` scheme. -/
noncomputable def frobeniusOnStructurePresheaf :
    X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom
    (ringFrobenius Γ(X, U.unop) p (IsCharacteristicP.cast_eq_zero U.unop))
  naturality {U V} i := by
    ext a
    change ringFrobenius Γ(X, V.unop) p
        (LSZ.IsCharacteristicP.cast_eq_zero V.unop) (X.presheaf.map i a) =
      X.presheaf.map i (ringFrobenius Γ(X, U.unop) p
        (LSZ.IsCharacteristicP.cast_eq_zero U.unop) a)
    rw [ringFrobenius_apply, ringFrobenius_apply, map_pow]

/-- The underlying morphism of presheafed spaces for absolute Frobenius.

It is reducible so that stalks over the identity map do not acquire opaque
transport terms. -/
noncomputable abbrev frobeniusPresheafedSpaceHom :
    X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := 𝟙 _
  c := frobeniusOnStructurePresheaf (p := p) X

@[simp]
lemma frobeniusPresheafedSpaceHom_base_apply (x : X) :
    (frobeniusPresheafedSpaceHom (p := p) X).base x = x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On every stalk, the map induced by absolute Frobenius is `p`-th power. -/
lemma frobeniusPresheafedSpaceHom_stalkMap_apply (x : X)
    (a : X.presheaf.stalk x) :
    (frobeniusPresheafedSpaceHom (p := p) X).stalkMap x a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  erw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
  change (X.presheaf.germ U x _).hom
      (ringFrobenius Γ(X, U) p
        (LSZ.IsCharacteristicP.cast_eq_zero U) s) =
    (X.presheaf.germ U x _).hom s ^ p
  rw [ringFrobenius_apply, map_pow]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The stalk maps of the Frobenius construction are local ring
homomorphisms. -/
lemma frobeniusPresheafedSpaceHom_isLocal (x : X) :
    IsLocalHom
      ((frobeniusPresheafedSpaceHom (p := p) X).stalkMap x).hom := by
  refine IsLocalHom.mk fun a ha ↦ ?_
  rw [frobeniusPresheafedSpaceHom_stalkMap_apply (p := p) X x a,
    isUnit_pow_iff ((Fact.out : Nat.Prime p).ne_zero)] at ha
  exact ha

/-- Absolute Frobenius as a morphism of locally ringed spaces. -/
noncomputable abbrev frobeniusLocallyRingedSpaceHom :
    X.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  AlgebraicGeometry.LocallyRingedSpace.homMk
    (InducedCategory.homMk (frobeniusPresheafedSpaceHom (p := p) X))
    (frobeniusPresheafedSpaceHom_isLocal (p := p) X)

/-- The absolute Frobenius `F_X : X ⟶ X` of a characteristic-`p` scheme. -/
noncomputable abbrev absoluteFrobenius : X ⟶ X :=
  AlgebraicGeometry.Scheme.Hom.mk
    (frobeniusLocallyRingedSpaceHom (p := p) X)

@[simp]
lemma absoluteFrobenius_toPshHom :
    (absoluteFrobenius (p := p) X).toPshHom =
      frobeniusPresheafedSpaceHom (p := p) X := rfl

@[simp]
lemma absoluteFrobenius_apply (x : X) :
    absoluteFrobenius (p := p) X x = x := rfl

/-- Absolute Frobenius fixes every open subset set-theoretically. -/
@[simp]
lemma absoluteFrobenius_preimage (U : X.Opens) :
    absoluteFrobenius (p := p) X ⁻¹ᵁ U = U := rfl

/-- Absolute Frobenius is affine: the inverse image of an affine open is the
same affine open. -/
instance absoluteFrobenius_isAffineHom :
    AlgebraicGeometry.IsAffineHom (absoluteFrobenius (p := p) X) where
  isAffine_preimage U hU := by
    rw [absoluteFrobenius_preimage (p := p) X U]
    exact hU

/-- On every open subset the map on functions is `a ↦ a ^ p`. -/
lemma absoluteFrobenius_app_apply (U : X.Opens) (a : Γ(X, U)) :
    (absoluteFrobenius (p := p) X).app U a = a ^ p := by
  change (absoluteFrobenius (p := p) X).toPshHom.c.app (.op U) a = a ^ p
  have h := absoluteFrobenius_toPshHom (p := p) X
  cases h
  change ringFrobenius Γ(X, U) p
      (LSZ.IsCharacteristicP.cast_eq_zero U) a = a ^ p
  exact ringFrobenius_apply Γ(X, U) p
    (LSZ.IsCharacteristicP.cast_eq_zero U) a

/-- In the affine chart of an affine open `U`, absolute Frobenius is
`Spec.map` of the `p`-power endomorphism on `Γ(U, 𝒪_X)`.

Together with `absoluteFrobenius_app_apply`, this is the precise scheme-level
statement that the restriction to every affine open is absolute Frobenius. -/
lemma absoluteFrobenius_on_affine (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    (hU.preimage (absoluteFrobenius (p := p) X)).isoSpec.hom ≫
        AlgebraicGeometry.Spec.map
          ((absoluteFrobenius (p := p) X).app U) =
      absoluteFrobenius (p := p) X ∣_ U ≫ hU.isoSpec.hom := by
  simpa only [AlgebraicGeometry.IsAffineOpen.isoSpec_hom] using
    (AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality
      (absoluteFrobenius (p := p) X) U)

end

end AlgebraicGeometry.Scheme
