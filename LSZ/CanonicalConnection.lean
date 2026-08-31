import LSZ.AbsoluteFrobenius
import LSZ.Objects
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The canonical Cartier connection in characteristic `p`

For a `k`-algebra `A` of characteristic `p` and an `A`-module `M`, this
file constructs

`  F_A^* M = A ⊗_{A,F_A} M`

with its canonical connection

`  ∇ᶜᵃⁿ_D (a ⊗ m) = D(a) ⊗ m.`

The two small wrapper types below only keep the two copies of `A` and `M`
definitionally distinct for Lean's typeclass elaborator.  They are equipped
with explicit equivalences back to `A` and `M`, and add no mathematical
input to the construction.
-/

open scoped TensorProduct ModuleCat.Algebra

namespace LSZ

universe u₁ u₂ u₃

noncomputable section

section Affine

variable (k : Type u₁) (A : Type u₂) (M : Type u₃) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [AddCommGroup M] [Module A M]
variable [CharP k p] [Fact p.Prime]

/-- A definitionally distinct copy of the source of affine Frobenius. -/
structure FrobeniusSource (k : Type u₁) (A : Type u₂) (p : ℕ) where
  down : A

/-- The tautological equivalence from the tagged Frobenius source to `A`. -/
def FrobeniusSource.equiv : FrobeniusSource k A p ≃ A where
  toFun := FrobeniusSource.down
  invFun := FrobeniusSource.mk
  left_inv := by rintro ⟨a⟩; rfl
  right_inv := by intro a; rfl

instance : CommRing (FrobeniusSource k A p) :=
  (FrobeniusSource.equiv k A p).commRing

/-- The tautological ring equivalence from the tagged source to `A`. -/
def FrobeniusSource.ringEquiv : FrobeniusSource k A p ≃+* A :=
  Equiv.ringEquiv (FrobeniusSource.equiv k A p)

/-- Functoriality of the tagged Frobenius source. -/
def FrobeniusSource.map {B : Type*} [CommRing B] (f : A →+* B) :
    FrobeniusSource k A p →+* FrobeniusSource k B p :=
  (FrobeniusSource.ringEquiv k B p).symm.toRingHom.comp
    (f.comp (FrobeniusSource.ringEquiv k A p).toRingHom)

@[simp]
lemma FrobeniusSource.map_down {B : Type*} [CommRing B]
    (f : A →+* B) (a : FrobeniusSource k A p) :
    (FrobeniusSource.map k A p f a).down = f a.down := rfl

/-- A definitionally distinct copy of the coefficient module. -/
structure FrobeniusCoefficient (M : Type u₃) where
  down : M

/-- The tautological equivalence from tagged coefficients to `M`. -/
def FrobeniusCoefficient.equiv : FrobeniusCoefficient M ≃ M where
  toFun := FrobeniusCoefficient.down
  invFun := FrobeniusCoefficient.mk
  left_inv := by rintro ⟨m⟩; rfl
  right_inv := by intro m; rfl

instance : AddCommGroup (FrobeniusCoefficient M) :=
  (FrobeniusCoefficient.equiv M).addCommGroup

instance : Module (FrobeniusSource k A p) (FrobeniusCoefficient M) := by
  letI : Module (FrobeniusSource k A p) M :=
    Module.compHom M (FrobeniusSource.ringEquiv k A p).toRingHom
  exact (FrobeniusCoefficient.equiv M).module (FrobeniusSource k A p)

/-- A semilinear map on coefficients, transported to the tagged copies. -/
def FrobeniusCoefficient.map {B : Type*} {N : Type*}
    [CommRing B] [AddCommGroup N] [Module B N]
    (f : A →+* B) (g : M →ₛₗ[f] N) :
    FrobeniusCoefficient M →ₛₗ[FrobeniusSource.map k A p f]
      FrobeniusCoefficient N where
  toFun m := FrobeniusCoefficient.mk (g m.down)
  map_add' := by
    intro m n
    apply (FrobeniusCoefficient.equiv N).injective
    exact map_add g m.down n.down
  map_smul' := by
    intro r m
    apply (FrobeniusCoefficient.equiv N).injective
    exact g.map_smulₛₗ r.down m.down

/-- The absolute Frobenius, with a tagged copy of `A` as source. -/
def frobeniusBaseMap : FrobeniusSource k A p →+* A :=
  (algebraFrobenius k A p).comp
    (FrobeniusSource.ringEquiv k A p).toRingHom

instance : Algebra (FrobeniusSource k A p) A :=
  (frobeniusBaseMap k A p).toAlgebra

instance : IsScalarTower (FrobeniusSource k A p)
    (FrobeniusSource k A p) A :=
  ⟨by
    intro r s a
    change frobeniusBaseMap k A p (r * s) * a =
      frobeniusBaseMap k A p r * (frobeniusBaseMap k A p s * a)
    rw [map_mul, mul_assoc]⟩

instance :
    IsScalarTower (FrobeniusSource k A p) (FrobeniusSource k A p)
      (FrobeniusCoefficient M) :=
  IsScalarTower.left (FrobeniusSource k A p)

instance : SMulCommClass (FrobeniusSource k A p) A A :=
  ⟨by
    intro r a b
    change frobeniusBaseMap k A p r * (a * b) =
      a * (frobeniusBaseMap k A p r * b)
    ring⟩

instance :
    Module A (TensorProduct (FrobeniusSource k A p) A
      (FrobeniusCoefficient M)) :=
  TensorProduct.leftModule
    (R := FrobeniusSource k A p) (R'' := A)
    (M := A) (N := FrobeniusCoefficient M)

/-- Frobenius pullback of an affine module, bundled with its outer
`A`-module structure.  This is canonically `A ⊗_{A,F_A} M`. -/
abbrev AffineFrobeniusPullback : ModuleCat A :=
  ModuleCat.of A
    (TensorProduct (FrobeniusSource k A p) A (FrobeniusCoefficient M))

namespace AffineFrobeniusPullback

/-- Insert an elementary tensor into the Frobenius pullback. -/
def tmul (a : A) (m : M) : AffineFrobeniusPullback k A M p :=
  a ⊗ₜ[FrobeniusSource k A p] FrobeniusCoefficient.mk m

section BaseChange

variable {B : Type*} {N : Type*}
variable [CommRing B] [Algebra k B] [AddCommGroup N] [Module B N]

/-- The first-factor semilinear map used by Frobenius base change. -/
def scalarBaseChange (f : A →+* B) :
    A →ₛₗ[FrobeniusSource.map k A p f] B where
  toFun := f
  map_add' := map_add f
  map_smul' := by
    intro r a
    change f (algebraFrobenius k A p r.down * a) =
      algebraFrobenius k B p (f r.down) * f a
    rw [map_mul, algebraFrobenius_apply, algebraFrobenius_apply, map_pow]

/-- Functorial base change on affine Frobenius pullbacks. -/
def baseChange (f : A →+* B) (g : M →ₛₗ[f] N) :
    AffineFrobeniusPullback k A M p →ₛₗ[f]
      AffineFrobeniusPullback k B N p where
  toFun := TensorProduct.map
    (scalarBaseChange (k := k) (A := A) (p := p) f)
    (FrobeniusCoefficient.map k A M p f g)
  map_add' := map_add _
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul a m =>
        simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul]
        change f (r * a) ⊗ₜ[FrobeniusSource k B p]
            (FrobeniusCoefficient.map k A M p f g) m =
          (f r * f a) ⊗ₜ[FrobeniusSource k B p]
            (FrobeniusCoefficient.map k A M p f g) m
        rw [map_mul]
    | add x y hx hy =>
        rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp]
lemma baseChange_tmul (f : A →+* B) (g : M →ₛₗ[f] N)
    (a : A) (m : FrobeniusCoefficient M) :
    baseChange (k := k) (A := A) (M := M) (p := p) f g
        (a ⊗ₜ[FrobeniusSource k A p] m) =
      f a ⊗ₜ[FrobeniusSource k B p]
        FrobeniusCoefficient.mk (g m.down) := by
  rfl

@[simp]
lemma baseChange_tmul_mk (f : A →+* B) (g : M →ₛₗ[f] N)
    (a : A) (m : M) :
    baseChange (k := k) (A := A) (M := M) (p := p) f g
        (tmul k A M p a m) =
      tmul k B N p (f a) (g m) := by
  rfl

/-- A base change whose ring and module maps are pointwise the identity is
the identity on the Frobenius pullback. -/
lemma baseChange_eq_self (f : A →+* A) (g : M →ₛₗ[f] M)
    (hf : ∀ a, f a = a) (hg : ∀ m, g m = m)
    (x : AffineFrobeniusPullback k A M p) :
    baseChange (k := k) (A := A) (M := M) (p := p) f g x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
      rw [baseChange_tmul]
      cases m with
      | mk m => rw [hf a, hg m]
  | add x y hx hy => rw [map_add, hx, hy]

/-- Pointwise functoriality of affine Frobenius base change.  The pointwise
hypotheses make this lemma usable when the three maps are only propositionally
identified by the functor laws of a presheaf. -/
lemma baseChange_comp_apply
    {C : Type*} {P : Type*}
    [CommRing C] [Algebra k C] [AddCommGroup P] [Module C P]
    (f₁ : A →+* B) (g₁ : M →ₛₗ[f₁] N)
    (f₂ : B →+* C) (g₂ : N →ₛₗ[f₂] P)
    (f₂₁ : A →+* C) (g₂₁ : M →ₛₗ[f₂₁] P)
    (hf : ∀ a, f₂₁ a = f₂ (f₁ a))
    (hg : ∀ m, g₂₁ m = g₂ (g₁ m))
    (x : AffineFrobeniusPullback k A M p) :
    baseChange (k := k) (A := A) (M := M) (p := p) f₂₁ g₂₁ x =
      baseChange (k := k) (A := B) (M := N) (p := p) f₂ g₂
        (baseChange (k := k) (A := A) (M := M) (p := p) f₁ g₁ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
      rw [baseChange_tmul, baseChange_tmul, baseChange_tmul]
      cases m with
      | mk m => rw [hf a, hg m]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end BaseChange

/-- A relative derivation kills every element in the image of Frobenius. -/
lemma derivation_frobenius_eq_zero (D : Derivation k A A) (a : A) :
    D (algebraFrobenius k A p a) = 0 := by
  rw [algebraFrobenius_apply, D.leibniz_pow]
  have hpA : (p : A) = 0 := by
    calc
      (p : A) = algebraMap k A (p : k) := by rw [map_natCast]
      _ = algebraMap k A 0 := by rw [CharP.cast_eq_zero]
      _ = 0 := map_zero _
  simpa [← Nat.cast_smul_eq_nsmul A, hpA]

/-- The additive operator underlying the canonical connection in direction
`D`.  Its well-definedness is precisely `D(a ^ p) = 0`. -/
def canonicalNablaAdd (D : Derivation k A A) :
    AffineFrobeniusPullback k A M p →+
      AffineFrobeniusPullback k A M p := by
  let P := AffineFrobeniusPullback k A M p
  let b :
      A →ₗ[FrobeniusSource k A p]
        (FrobeniusCoefficient M →ₗ[FrobeniusSource k A p] P) :=
    { toFun := fun a ↦
        { toFun := fun m ↦ D a ⊗ₜ[FrobeniusSource k A p] m
          map_add' := by
            intro m n
            exact TensorProduct.tmul_add _ _ _
          map_smul' := by
            intro r m
            rw [TensorProduct.tmul_smul]
            exact (TensorProduct.smul_tmul' r (D a) m).symm }
      map_add' := by
        intro a b
        ext m
        change D (a + b) ⊗ₜ[FrobeniusSource k A p] m =
          D a ⊗ₜ[FrobeniusSource k A p] m +
            D b ⊗ₜ[FrobeniusSource k A p] m
        rw [map_add, TensorProduct.add_tmul]
      map_smul' := by
        intro r a
        ext m
        change D (frobeniusBaseMap k A p r * a) ⊗ₜ[FrobeniusSource k A p] m =
          r • (D a ⊗ₜ[FrobeniusSource k A p] m : P)
        rw [D.leibniz, show D (frobeniusBaseMap k A p r) = 0 by
              exact derivation_frobenius_eq_zero k A p D r.down,
          smul_zero, add_zero, TensorProduct.smul_tmul']
        change (frobeniusBaseMap k A p r * D a) ⊗ₜ[FrobeniusSource k A p] m =
          (frobeniusBaseMap k A p r * D a) ⊗ₜ[FrobeniusSource k A p] m
        rfl }
  exact (TensorProduct.lift b).toAddMonoidHom

@[simp]
lemma canonicalNablaAdd_tmul (D : Derivation k A A) (a : A)
    (m : FrobeniusCoefficient M) :
    canonicalNablaAdd k A M p D (a ⊗ₜ[FrobeniusSource k A p] m) =
      D a ⊗ₜ[FrobeniusSource k A p] m := by
  rfl

@[simp]
lemma canonicalNablaAdd_tmul_mk (D : Derivation k A A) (a : A) (m : M) :
    canonicalNablaAdd k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := by
  rfl

/-- Leibniz rule for the additive operator underlying the canonical
connection. -/
lemma canonicalNablaAdd_leibniz (D : Tangent k A) (a : A)
    (x : AffineFrobeniusPullback k A M p) :
    canonicalNablaAdd k A M p D (a • x) =
      a • canonicalNablaAdd k A M p D x + D a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero, add_zero]
  | tmul b m =>
      change D (a * b) ⊗ₜ[FrobeniusSource k A p] m =
        a • (D b ⊗ₜ[FrobeniusSource k A p] m :
          AffineFrobeniusPullback k A M p) +
          D a • (b ⊗ₜ[FrobeniusSource k A p] m :
            AffineFrobeniusPullback k A M p)
      simp only [Derivation.leibniz, TensorProduct.smul_tmul',
        TensorProduct.add_tmul]
      rw [show b • D a = D a • b by
        simp only [smul_eq_mul, mul_comm], add_comm]
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy, smul_add, smul_add]
      abel

/-- The canonical connection operator in one tangent direction. -/
def canonicalNablaEnd (D : Derivation k A A) :
    Module.End k (AffineFrobeniusPullback k A M p) where
  toFun := canonicalNablaAdd k A M p D
  map_add' := map_add _
  map_smul' := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul a m =>
        rw [TensorProduct.smul_tmul', Algebra.smul_def,
          canonicalNablaAdd_tmul, canonicalNablaAdd_tmul,
          TensorProduct.smul_tmul', Algebra.smul_def,
          D.leibniz, D.map_algebraMap]
        simp only [smul_zero, RingHom.id_apply, smul_eq_mul, mul_zero, add_zero]
    | add x y hx hy =>
        rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp]
lemma canonicalNablaEnd_tmul (D : Derivation k A A) (a : A)
    (m : FrobeniusCoefficient M) :
    canonicalNablaEnd k A M p D (a ⊗ₜ[FrobeniusSource k A p] m) =
      D a ⊗ₜ[FrobeniusSource k A p] m := by
  rfl

/-- The canonical connection, linear in the tangent-vector argument. -/
def canonicalNabla :
    Tangent k A →ₗ[A]
      Module.End k (AffineFrobeniusPullback k A M p) where
  toFun := canonicalNablaEnd k A M p
  map_add' := by
    intro D E
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.add_apply, add_zero]
    | tmul a m =>
        change (D + E) a ⊗ₜ[FrobeniusSource k A p] m =
          D a ⊗ₜ[FrobeniusSource k A p] m +
            E a ⊗ₜ[FrobeniusSource k A p] m
        rw [Derivation.add_apply, TensorProduct.add_tmul]
    | add x y hx hy =>
        simpa only [map_add, LinearMap.add_apply] using
          congrArg₂ (fun u v ↦ u + v) hx hy
  map_smul' := by
    intro r D
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.smul_apply, smul_zero]
    | tmul a m =>
        change (r * D a) ⊗ₜ[FrobeniusSource k A p] m =
          r • (D a ⊗ₜ[FrobeniusSource k A p] m :
            AffineFrobeniusPullback k A M p)
        rw [TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy =>
        simpa only [map_add, LinearMap.smul_apply, smul_add] using
          congrArg₂ (fun u v ↦ u + v) hx hy

@[simp]
lemma canonicalNabla_tmul (D : Tangent k A) (a : A)
    (m : FrobeniusCoefficient M) :
    canonicalNabla k A M p D (a ⊗ₜ[FrobeniusSource k A p] m) =
      D a ⊗ₜ[FrobeniusSource k A p] m := by
  rfl

@[simp]
lemma canonicalNabla_tmul_mk (D : Tangent k A) (a : A) (m : M) :
    canonicalNabla k A M p D (tmul k A M p a m) =
      tmul k A M p (D a) m := by
  rfl

/-- Leibniz rule for the canonical connection. -/
lemma canonicalNabla_leibniz (D : Tangent k A) (a : A)
    (x : AffineFrobeniusPullback k A M p) :
    canonicalNabla k A M p D (a • x) =
      a • canonicalNabla k A M p D x + D a • x := by
  exact canonicalNablaAdd_leibniz k A M p D a x

/-- Vanishing curvature of the canonical connection. -/
lemma canonicalNabla_flat (D E : Tangent k A)
    (x : AffineFrobeniusPullback k A M p) :
    canonicalNabla k A M p ⁅D, E⁆ x =
      canonicalNabla k A M p D (canonicalNabla k A M p E x) -
        canonicalNabla k A M p E (canonicalNabla k A M p D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | tmul a m =>
      change ⁅D, E⁆ a ⊗ₜ[FrobeniusSource k A p] m =
        D (E a) ⊗ₜ[FrobeniusSource k A p] m -
          E (D a) ⊗ₜ[FrobeniusSource k A p] m
      rw [Derivation.commutator_apply, TensorProduct.sub_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, map_add, hx, hy]
      abel

/-- The affine Frobenius pullback equipped with its canonical flat
connection. -/
def canonicalConnection :
    IntegrableConnection k A (AffineFrobeniusPullback k A M p) where
  nabla := canonicalNabla k A M p
  leibniz := canonicalNabla_leibniz k A M p
  flat := canonicalNabla_flat k A M p

end AffineFrobeniusPullback

end Affine

end

end LSZ
