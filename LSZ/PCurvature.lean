import LSZ.PositiveCharacteristic

/-!
# The p-curvature of an integrable connection

The ordinary connection category remains characteristic-free.  This file
specializes to the positive characteristic of the base field and constructs
the p-curvature from the canonical restricted power of vector fields.
-/

open CategoryTheory Finset Nat TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u v w

section IteratedLeibniz

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

/-- Generalized Leibniz formula for repeated application of an additive
connection operator. -/
theorem connection_iterate_smul (D : Derivation R A A)
    (N : Module.End ℤ M)
    (hN : ∀ (a : A) (m : M), N (a • m) = a • N m + D a • m)
    (n : ℕ) (a : A) (m : M) :
    N^[n] (a • m) =
      ∑ ij ∈ antidiagonal n,
        choose n ij.1 • ((D^[ij.1] a) • (N^[ij.2] m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (M := M) (fun i j => (D^[i] a) • (N^[j] m)) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul,
      hN, smul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- Range-indexed generalized Leibniz formula for a connection operator. -/
theorem connection_iterate_smul' (D : Derivation R A A)
    (N : Module.End ℤ M)
    (hN : ∀ (a : A) (m : M), N (a • m) = a • N m + D a • m)
    (n : ℕ) (a : A) (m : M) :
    N^[n] (a • m) =
      ∑ i ∈ range (n + 1),
        choose n i • ((D^[i] a) • (N^[n - i] m)) := by
  rw [connection_iterate_smul D N hN n a m]
  exact sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • ((D^[i] a) • (N^[j] m))) n

/-- At a prime characteristic, all mixed terms in the generalized Leibniz
formula vanish. -/
theorem connection_prime_smul (D : Derivation R A A)
    (N : Module.End ℤ M)
    (hN : ∀ (a : A) (m : M), N (a • m) = a • N m + D a • m)
    (p : ℕ) [CharP A p] (hp : p.Prime) (a : A) (m : M) :
    N^[p] (a • m) = a • N^[p] m + D^[p] a • m := by
  let f : ℕ → M := fun i => choose p i • ((D^[i] a) • (N^[p - i] m))
  have hsubset : ({0, p} : Finset ℕ) ⊆ range (p + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hoff : ∀ i ∈ range (p + 1), i ∉ ({0, p} : Finset ℕ) → f i = 0 := by
    intro i hiRange hiEndpoints
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      simp at hiEndpoints
    have hip : i ≠ p := by
      intro hi
      subst i
      simp at hiEndpoints
    have hip' : i < p := by
      simp only [mem_range] at hiRange
      omega
    have hcast : (choose p i : A) = 0 :=
      (CharP.cast_eq_zero_iff A p (choose p i)).2
        (hp.dvd_choose_self hi0 hip')
    dsimp [f]
    rw [← Nat.cast_smul_eq_nsmul A]
    simp [hcast]
  calc
    N^[p] (a • m) = ∑ i ∈ range (p + 1), f i := by
      simpa [f] using connection_iterate_smul' D N hN p a m
    _ = ∑ i ∈ ({0, p} : Finset ℕ), f i :=
      (sum_subset hsubset hoff).symm
    _ = a • N^[p] m + D^[p] a • m := by
      rw [sum_insert (by simpa using hp.ne_zero.symm), sum_singleton]
      simp [f]

/-- Field-base version of `connection_prime_smul`, including the case in
which the coefficient algebra is the zero ring. -/
theorem connection_prime_smul_field {K : Type u} [Field K] [Algebra K A]
    (D : Derivation K A A) (N : Module.End ℤ M)
    (hN : ∀ (a : A) (m : M), N (a • m) = a • N m + D a • m)
    (p : ℕ) [CharP K p] (hp : p.Prime) (a : A) (m : M) :
    N^[p] (a • m) = a • N^[p] m + D^[p] a • m := by
  classical
  by_cases hA : Nontrivial A
  · letI : Nontrivial A := hA
    letI : CharP A p :=
      charP_of_injective_algebraMap (algebraMap K A).injective p
    exact connection_prime_smul D N hN p hp a m
  · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    haveI : Subsingleton M := Module.subsingleton A M
    exact Subsingleton.elim _ _

end IteratedLeibniz

namespace SmoothScheme.IntegrableConnection

noncomputable section

variable {k : Type u} [Field k] [NeZero (ringChar k)]
variable {X : LSZ.SmoothScheme k} (C : X.IntegrableConnection)

local instance characteristicPrime : Fact (ringChar k).Prime :=
  CharP.char_is_prime_of_pos k (ringChar k)

/-- The standard-sign p-curvature operator
`psi(D) = nabla_D^p - nabla_(D^[p])`, initially as an additive
endomorphism of sections. -/
def pCurvatureAdditive (U : X.scheme.Opens) (D : X.VectorField U) :
    Module.End ℤ Γ(C.carrier, U) :=
  C.nabla U D ^ ringChar k - C.nabla U D.pPower

@[simp]
lemma pCurvatureAdditive_apply (U : X.scheme.Opens) (D : X.VectorField U)
    (m : Γ(C.carrier, U)) :
    C.pCurvatureAdditive U D m =
      (C.nabla U D)^[ringChar k] m - C.nabla U D.pPower m := by
  simp [pCurvatureAdditive, Module.End.pow_apply]

/-- For fixed `D`, p-curvature is additive in the module section. -/
lemma pCurvatureAdditive_add (U : X.scheme.Opens) (D : X.VectorField U)
    (m n : Γ(C.carrier, U)) :
    C.pCurvatureAdditive U D (m + n) =
      C.pCurvatureAdditive U D m + C.pCurvatureAdditive U D n :=
  map_add _ _ _

/-- First linearity assertion: for fixed `D`, p-curvature is linear in the
module section. -/
lemma pCurvatureAdditive_smul (U : X.scheme.Opens) (D : X.VectorField U)
    (a : Γ(X.scheme, U)) (m : Γ(C.carrier, U)) :
    C.pCurvatureAdditive U D (a • m) =
      a • C.pCurvatureAdditive U D m := by
  rw [pCurvatureAdditive_apply, pCurvatureAdditive_apply]
  rw [connection_prime_smul_field D.act (C.nabla U D)
    (C.leibniz U D) (ringChar k) characteristicPrime.out]
  rw [C.leibniz U D.pPower]
  simp only [SmoothScheme.VectorField.pPower_act]
  module

/-- For fixed `D`, p-curvature as an honest linear endomorphism of the
module of sections. -/
def pCurvature (U : X.scheme.Opens) (D : X.VectorField U) :
    Module.End Γ(X.scheme, U) Γ(C.carrier, U) where
  toFun := C.pCurvatureAdditive U D
  map_add' := map_add _
  map_smul' := C.pCurvatureAdditive_smul U D

@[simp]
lemma pCurvature_apply (U : X.scheme.Opens) (D : X.VectorField U)
    (m : Γ(C.carrier, U)) :
    C.pCurvature U D m =
      (C.nabla U D)^[ringChar k] m - C.nabla U D.pPower m :=
  C.pCurvatureAdditive_apply U D m

/-- P-curvature commutes with restriction of both the vector field and the
module section. -/
lemma pCurvature_restrict {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U) (m : Γ(C.carrier, U)) :
    C.carrier.presheaf.map (homOfLE hVU).op (C.pCurvature U D m) =
      C.pCurvature V (D.restrict hVU)
        (C.carrier.presheaf.map (homOfLE hVU).op m) := by
  simp only [pCurvature_apply, map_sub]
  rw [map_iterate
    (C.carrier.presheaf.map (homOfLE hVU).op)
    (C.nabla U D) (C.nabla V (D.restrict hVU))
    (C.nabla_restrict hVU D) (ringChar k) m]
  rw [C.nabla_restrict hVU D.pPower m]
  rw [SmoothScheme.VectorField.pPower_restrict]

/-- A vector field on an arbitrary open `U` gives p-curvature as an
`O_U`-linear endomorphism of the restriction of the coefficient sheaf to
the over-site of `U`.  Thus no global extension of the vector field is
required. -/
def pCurvatureEndomorphismOn (U : X.scheme.Opens) (D : X.VectorField U) :
    C.carrier.over U ⟶ C.carrier.over U where
  val :=
    { app := fun V => by
        exact ModuleCat.homMk
          (AddCommGrpCat.ofHom
            { toFun := fun m =>
                C.pCurvatureAdditive V.unop.left
                  (D.restrict (leOfHom V.unop.hom)) m
              map_zero' := map_zero _
              map_add' := map_add _ })
          (by
            intro a
            ext m
            exact (C.pCurvatureAdditive_smul V.unop.left
              (D.restrict (leOfHom V.unop.hom)) a m).symm)
      naturality := by
        intro V W f
        ext m
        change C.pCurvature W.unop.left
            (D.restrict (leOfHom W.unop.hom))
            (C.carrier.presheaf.map f.unop.left.op m) =
          C.carrier.presheaf.map f.unop.left.op
            (C.pCurvature V.unop.left
              (D.restrict (leOfHom V.unop.hom)) m)
        let hWV : W.unop.left ≤ V.unop.left := leOfHom f.unop.left
        have hf : f.unop.left = homOfLE hWV := Subsingleton.elim _ _
        rw [hf]
        have hD :
            (D.restrict (leOfHom V.unop.hom)).restrict hWV =
              D.restrict (leOfHom W.unop.hom) := by
          ext Z hZ a
          rfl
        rw [← hD]
        exact (C.pCurvature_restrict hWV
          (D.restrict (leOfHom V.unop.hom)) m).symm }

@[simp]
lemma pCurvatureEndomorphismOn_app (U : X.scheme.Opens)
    (D : X.VectorField U) (V : (Over U)ᵒᵖ)
    (m : (C.carrier.over U).val.obj V) :
    (C.pCurvatureEndomorphismOn U D).val.app V m =
      C.pCurvature V.unop.left
        (D.restrict (leOfHom V.unop.hom)) m := rfl

/-- Second linearity assertion: every component of the p-curvature sheaf
morphism is linear over the corresponding ring of functions. -/
lemma pCurvatureEndomorphismOn_smul (U : X.scheme.Opens)
    (D : X.VectorField U) (V : (Over U)ᵒᵖ)
    (a : (X.scheme.ringCatSheaf.over U).obj.obj V)
    (m : (C.carrier.over U).val.obj V) :
    (C.pCurvatureEndomorphismOn U D).val.app V (a • m) =
      a • (C.pCurvatureEndomorphismOn U D).val.app V m := by
  exact map_smul _ a m

/-- For a global vector field, p-curvature is an `O_X`-linear morphism of
sheaves, not merely a family of additive maps on sections. -/
def pCurvatureEndomorphism (D : X.VectorField ⊤) :
    C.carrier ⟶ C.carrier where
  val :=
    { app := fun U => ModuleCat.ofHom
        (C.pCurvature U.unop (D.restrict le_top))
      naturality := by
        intro U V f
        ext m
        change C.pCurvature V.unop (D.restrict le_top)
            (C.carrier.presheaf.map f m) =
          C.carrier.presheaf.map f
            (C.pCurvature U.unop (D.restrict le_top) m)
        let hVU : V.unop ≤ U.unop := leOfHom f.unop
        rw [show f = (homOfLE hVU).op from Subsingleton.elim _ _]
        have hD :
            (D.restrict (show U.unop ≤ ⊤ from le_top)).restrict hVU =
              D.restrict (show V.unop ≤ ⊤ from le_top) := by
          ext W hW a
          rfl
        rw [← hD]
        exact (C.pCurvature_restrict hVU
          (D.restrict (show U.unop ≤ ⊤ from le_top)) m).symm }

@[simp]
lemma pCurvatureEndomorphism_app (D : X.VectorField ⊤)
    (U : X.scheme.Opens) (m : Γ(C.carrier, U)) :
    (C.pCurvatureEndomorphism D).app U m =
      C.pCurvature U (D.restrict le_top) m := rfl

end

end SmoothScheme.IntegrableConnection

end LSZ
