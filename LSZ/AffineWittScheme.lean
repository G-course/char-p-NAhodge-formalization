import LSZ.GeometricWittLift
import LSZ.AffineWittLift
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# From affine Witt lifts to geometric Frobenius lifts

For a smooth `W₂(k)`-algebra `B`, this file constructs the smooth affine
special fibre `Spec (k ⊗[W₂(k)] B)` and its geometric `W₂(k)`-lift.
An algebraic Frobenius lift on `B` then gives a scheme-theoretic Frobenius
lift.  The reduction condition is proved: after transport through the
special-fibre isomorphism, the induced morphism is the absolute Frobenius.
-/

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

namespace LSZ.AffineWittLift

universe u

noncomputable section

variable (p : ℕ) (k B : Type u)
variable [Field k] [CharP k p] [Fact p.Prime]
variable [CommRing B] [Algebra (W₂ p k) B]

private abbrev A := SpecialFiber p k B
private abbrev P := B ⊗[W₂ p k] k

lemma p_eq_zero_baseChange : (p : P p k B) = 0 := by
  let i : k →+* P p k B :=
    (Algebra.TensorProduct.includeRight :
      k →ₐ[W₂ p k] P p k B).toRingHom
  calc
    (p : P p k B) = i (p : k) := (map_natCast i p).symm
    _ = i 0 := congrArg i (CharP.cast_eq_zero k p)
    _ = 0 := map_zero i

/-- Absolute Frobenius on the tensor product `B ⊗[W₂(k)] k`. -/
def baseChangedFrobenius : P p k B →+* P p k B :=
  LSZ.ringFrobenius (P p k B) p (p_eq_zero_baseChange p k B)

/-- The spectrum isomorphism induced by commuting the two tensor factors. -/
def tensorCommSpecIso :
    AlgebraicGeometry.Spec (.of (B ⊗[W₂ p k] k)) ≅
      AlgebraicGeometry.Spec (.of (A p k B)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (Algebra.TensorProduct.comm (W₂ p k) k B).toRingEquiv.toCommRingCatIso.op

omit [CharP k p] in
lemma tensorCommSpecIso_hom :
    (tensorCommSpecIso p k B).hom =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.comm (W₂ p k) k B).toRingEquiv.toRingHom) := rfl

variable [Algebra.Smooth (W₂ p k) B]

/-- The smooth affine `k`-scheme obtained as the special fibre of `B`. -/
def specialFiberSmoothScheme : LSZ.SmoothScheme k where
  toScheme := AlgebraicGeometry.Spec (.of (A p k B))
  structureMap := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap k (A p k B)))
  smooth := by
    apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)
      (Q := RingHom.Smooth)).2
    change (algebraMap k (A p k B)).Smooth
    rw [RingHom.smooth_algebraMap]
    letI : Algebra.Smooth k (A p k B) :=
      Algebra.Smooth.baseChange (R := W₂ p k) (A := B) (B := k)
    exact inferInstance
  separated := by infer_instance

/-- The pullback special fibre of `Spec B` identified with
`Spec (k ⊗[W₂(k)] B)`. -/
def specialFiberIso :
    pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
        (LSZ.specialFiberPoint p k) ≅
      (specialFiberSmoothScheme p k B).scheme := by
  change pullback
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) k))) ≅
    AlgebraicGeometry.Spec (.of (A p k B))
  exact (AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k).trans
    (tensorCommSpecIso p k B)

omit [CharP k p] [Algebra.Smooth (W₂ p k) B] in
lemma tensorCommSpecIso_hom_structureMap :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.comm (W₂ p k) k B).toRingEquiv.toRingHom) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap k (A p k B))) =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            k →ₐ[W₂ p k] B ⊗[W₂ p k] k).toRingHom) := by
  rw [← AlgebraicGeometry.Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  ext x
  rfl

omit [CharP k p] in
lemma specialFiberIso_over :
    (specialFiberIso p k B).hom ≫
        (specialFiberSmoothScheme p k B).structureMap =
      pullback.snd
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
        (LSZ.specialFiberPoint p k) := by
  change ((AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k).trans
      (tensorCommSpecIso p k B)).hom ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap k (A p k B))) =
    pullback.snd
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) k)))
  rw [Iso.trans_hom, Category.assoc, tensorCommSpecIso_hom,
    tensorCommSpecIso_hom_structureMap]
  exact AlgebraicGeometry.pullbackSpecIso_hom_snd (W₂ p k) B k

lemma absoluteFrobenius_eq_specMap :
    AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
        (specialFiberSmoothScheme p k B).scheme =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p)) := by
  letI : LSZ.IsCharacteristicP
      (AlgebraicGeometry.Spec (.of (A p k B))) p :=
    inferInstanceAs
      (LSZ.IsCharacteristicP (specialFiberSmoothScheme p k B).scheme p)
  change AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
      (AlgebraicGeometry.Spec (.of (A p k B))) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p))
  apply AlgebraicGeometry.ext_of_isAffine
  ext a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (.of (A p k B))).hom).injective
  have hF := AlgebraicGeometry.Scheme.absoluteFrobenius_app_apply
    (p := p) (AlgebraicGeometry.Spec (.of (A p k B))) ⊤ a
  change (AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
    (AlgebraicGeometry.Spec (.of (A p k B)))).appTop a = a ^ p at hF
  rw [hF]
  rw [map_pow]
  change (AlgebraicGeometry.Scheme.ΓSpecIso (.of (A p k B))).hom a ^ p =
    (AlgebraicGeometry.Scheme.ΓSpecIso (.of (A p k B))).hom
      ((AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p))).appTop a)
  rw [← CommRingCat.comp_apply,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality]
  rfl

/-- A smooth affine algebra lift regarded as geometric `W₂(k)`-lifting
data for its special fibre. -/
def toSchemeW₂Lift :
    (specialFiberSmoothScheme p k B).W₂Lift (p := p) where
  lift := AlgebraicGeometry.Spec (.of B)
  structureMap := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (W₂ p k) B))
  smooth := by
    apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)
      (Q := RingHom.Smooth)).2
    change (algebraMap (W₂ p k) B).Smooth
    rw [RingHom.smooth_algebraMap]
    exact inferInstance
  specialFiberIso := specialFiberIso p k B
  specialFiberIso_over := specialFiberIso_over p k B

namespace Frobenius

variable [PerfectField k]
variable (Phi : Frobenius p k B)

omit [PerfectField k] in
lemma baseChangedFrobenius_includeLeft (b : B) :
    baseChangedFrobenius p k B
        (Algebra.TensorProduct.includeLeftRingHom (R := W₂ p k) (A := B) (B := k) b) =
      Algebra.TensorProduct.includeLeftRingHom (R := W₂ p k) (A := B) (B := k)
        (Phi.map b) := by
  rw [baseChangedFrobenius, LSZ.ringFrobenius_apply]
  have h := congrArg (Algebra.TensorProduct.comm (W₂ p k) k B)
    (Phi.map_specialFiber b)
  simpa using h.symm

omit [Algebra.Smooth (W₂ p k) B] [PerfectField k] in
lemma baseChangedFrobenius_includeRight (c : k) :
    baseChangedFrobenius p k B
        ((Algebra.TensorProduct.includeRight :
          k →ₐ[W₂ p k] P p k B) c) =
      (Algebra.TensorProduct.includeRight :
        k →ₐ[W₂ p k] P p k B) (frobenius k p c) := by
  rw [baseChangedFrobenius, LSZ.ringFrobenius_apply]
  rw [← map_pow]
  rfl

omit [PerfectField k] in
lemma specMap_over :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map) ≫
        (toSchemeW₂Lift p k B).structureMap =
      (toSchemeW₂Lift p k B).structureMap ≫ LSZ.w₂FrobeniusSpec p k := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) B)) =
    AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (W₂ p k) B)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (LSZ.w₂Frobenius p k))
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  ext r
  exact Phi.map_base r

/-- The morphism on the explicit pullback special fibre induced by an
algebraic Frobenius lift. -/
def specialFiberMap :
    pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) k))) ⟶
      pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) k))) :=
  pullback.lift
    (pullback.fst _ _ ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map))
    (pullback.snd _ _ ≫ LSZ.fieldFrobeniusSpec p k)
    (by
      change (pullback.fst
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
          (LSZ.specialFiberPoint p k) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map)) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (W₂ p k) B)) =
        (pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
          (LSZ.specialFiberPoint p k) ≫ LSZ.fieldFrobeniusSpec p k) ≫
            LSZ.specialFiberPoint p k
      have hLift := specMap_over p k B Phi
      change AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (W₂ p k) B)) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (W₂ p k) B)) ≫
          LSZ.w₂FrobeniusSpec p k at hLift
      rw [Category.assoc, hLift]
      rw [← Category.assoc (pullback.fst _ _)
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (W₂ p k) B)))]
      rw [pullback.condition]
      rw [Category.assoc, Category.assoc,
        LSZ.specialFiberPoint_frobenius])

omit [PerfectField k] in
@[reassoc (attr := simp)]
lemma specialFiberMap_fst :
    specialFiberMap p k B Phi ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map) := by
  exact pullback.lift_fst _ _ _

omit [PerfectField k] in
@[reassoc (attr := simp)]
lemma specialFiberMap_snd :
    specialFiberMap p k B Phi ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ LSZ.fieldFrobeniusSpec p k := by
  exact pullback.lift_snd _ _ _

omit [PerfectField k] in
/-- Under `pullbackSpecIso`, the induced special-fibre map is the `p`-power
endomorphism of `B ⊗[W₂(k)] k`. -/
lemma pullbackSpecIso_conjugation :
    (AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k).inv ≫
          specialFiberMap p k B Phi ≫
        (AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k).hom =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (baseChangedFrobenius p k B)) := by
  let e := AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k
  have hsf : specialFiberMap p k B Phi =
      e.hom ≫ AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫ e.inv := by
    apply pullback.hom_ext
    · rw [specialFiberMap_fst]
      rw [Category.assoc, Category.assoc,
        AlgebraicGeometry.pullbackSpecIso_inv_fst]
      have hMap :
          AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫
              AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom
                  (Algebra.TensorProduct.includeLeftRingHom
                    (R := W₂ p k) (A := B) (B := k))) =
            AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom
                  (Algebra.TensorProduct.includeLeftRingHom
                    (R := W₂ p k) (A := B) (B := k))) ≫
              AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map) := by
        rw [← AlgebraicGeometry.Spec.map_comp,
          ← AlgebraicGeometry.Spec.map_comp]
        rw [AlgebraicGeometry.Spec.map_inj]
        ext b
        exact baseChangedFrobenius_includeLeft p k B Phi b
      rw [hMap]
      rw [← Category.assoc,
        AlgebraicGeometry.pullbackSpecIso_hom_fst]
    · rw [specialFiberMap_snd]
      rw [Category.assoc, Category.assoc,
        AlgebraicGeometry.pullbackSpecIso_inv_snd]
      have hMap :
          AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫
              AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom
                  ((Algebra.TensorProduct.includeRight :
                    k →ₐ[W₂ p k] P p k B) : k →+* P p k B)) =
            AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom
                  ((Algebra.TensorProduct.includeRight :
                    k →ₐ[W₂ p k] P p k B) : k →+* P p k B)) ≫
              AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (frobenius k p)) := by
        rw [← AlgebraicGeometry.Spec.map_comp,
          ← AlgebraicGeometry.Spec.map_comp]
        rw [AlgebraicGeometry.Spec.map_inj]
        ext c
        exact baseChangedFrobenius_includeRight p k B c
      change pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (W₂ p k) B)))
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (W₂ p k) k))) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (frobenius k p)) =
        e.hom ≫
          (AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫
            AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom
                ((Algebra.TensorProduct.includeRight :
                  k →ₐ[W₂ p k] P p k B) : k →+* P p k B)))
      rw [hMap]
      rw [← Category.assoc,
        AlgebraicGeometry.pullbackSpecIso_hom_snd]
  change e.inv ≫ specialFiberMap p k B Phi ≫ e.hom = _
  rw [hsf]
  simp only [Category.assoc, e.inv_hom_id_assoc]
  rw [e.inv_hom_id, Category.comp_id]

omit [CharP k p] [PerfectField k] [Algebra.Smooth (W₂ p k) B] in
lemma tensorCommSpecIso_inv :
    (tensorCommSpecIso p k B).inv =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.comm
          (W₂ p k) k B).symm.toRingEquiv.toRingHom) := rfl

omit [Algebra.Smooth (W₂ p k) B] [PerfectField k] in
lemma tensorComm_conjugation :
    (tensorCommSpecIso p k B).inv ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫
        (tensorCommSpecIso p k B).hom =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p)) := by
  rw [tensorCommSpecIso_inv, tensorCommSpecIso_hom]
  rw [← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  rw [AlgebraicGeometry.Spec.map_inj]
  apply ConcreteCategory.hom_ext
  intro x
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  change (Algebra.TensorProduct.comm (W₂ p k) k B).symm
      (baseChangedFrobenius p k B
        ((Algebra.TensorProduct.comm (W₂ p k) k B) x)) =
    LSZ.algebraFrobenius k (A p k B) p x
  rw [LSZ.algebraFrobenius_apply, baseChangedFrobenius,
    LSZ.ringFrobenius_apply]
  rw [← map_pow]
  exact (Algebra.TensorProduct.comm
    (W₂ p k) k B).symm_apply_apply (x ^ p)

omit [PerfectField k] in
/-- Transporting the induced special-fibre map to
`Spec (k ⊗[W₂(k)] B)` gives its absolute Frobenius. -/
lemma specialFiberMap_reduction :
    (specialFiberIso p k B).inv ≫
          specialFiberMap p k B Phi ≫
        (specialFiberIso p k B).hom =
      AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
        (specialFiberSmoothScheme p k B).scheme := by
  letI : LSZ.IsCharacteristicP
      (AlgebraicGeometry.Spec (.of (A p k B))) p :=
    inferInstanceAs
      (LSZ.IsCharacteristicP (specialFiberSmoothScheme p k B).scheme p)
  let e := AlgebraicGeometry.pullbackSpecIso (W₂ p k) B k
  let c := tensorCommSpecIso p k B
  change (e.trans c).inv ≫ specialFiberMap p k B Phi ≫
      (e.trans c).hom =
    AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
      (AlgebraicGeometry.Spec (.of (A p k B)))
  calc
    (e.trans c).inv ≫ specialFiberMap p k B Phi ≫
        (e.trans c).hom =
      c.inv ≫
          (e.inv ≫ specialFiberMap p k B Phi ≫ e.hom) ≫
        c.hom := by
          simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    _ = c.inv ≫
          AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (baseChangedFrobenius p k B)) ≫
        c.hom := by
          rw [pullbackSpecIso_conjugation]
    _ = AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p)) := by
      simpa only [c] using tensorComm_conjugation p k B
    _ = AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
        (AlgebraicGeometry.Spec (.of (A p k B))) := by
      change AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (LSZ.algebraFrobenius k (A p k B) p)) =
        AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
          (specialFiberSmoothScheme p k B).scheme
      exact (absoluteFrobenius_eq_specMap p k B).symm

/-- An affine algebraic Frobenius lift determines the corresponding genuine
scheme-theoretic Frobenius lift; its reduction is proved to be absolute
Frobenius rather than supplied as an extra field. -/
def toSchemeFrobeniusLift :
    (specialFiberSmoothScheme p k B).FrobeniusLift
      (toSchemeW₂Lift p k B) where
  liftFrob := AlgebraicGeometry.Spec.map (CommRingCat.ofHom Phi.map)
  liftFrob_over := specMap_over p k B Phi
  reduction_eq := by
    change (specialFiberIso p k B).inv ≫
          specialFiberMap p k B Phi ≫
        (specialFiberIso p k B).hom =
      AlgebraicGeometry.Scheme.absoluteFrobenius (p := p)
        (specialFiberSmoothScheme p k B).scheme
    exact specialFiberMap_reduction p k B Phi

end Frobenius

end

end LSZ.AffineWittLift
