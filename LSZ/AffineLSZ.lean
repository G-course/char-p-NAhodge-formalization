import LSZ.StandardCanonicalConnection

/-!
# The affine LSZ transform for a fixed divided Frobenius lift

This file separates the algebraic construction from its scheme-theoretic
realization.  The coefficient module is pulled back by the absolute
Frobenius using mathlib's `ModuleCat.extendScalars`.
-/

open CategoryTheory
open scoped ModuleCat.Algebra ChangeOfRings TensorProduct

namespace LSZ

universe u

noncomputable section

namespace AffineObject

variable (k : Type u) (A : Type u)
variable [Field k] [CommRing A] [Algebra k A]

/-- An unrestricted integrable Higgs module over the affine algebra `A`. -/
structure IntegrableHiggs where
  carrier : ModuleCat.{u} A
  theta : Tangent k A →ₗ[A] Module.End A carrier
  integrable (D E : Tangent k A) (m : carrier) :
    theta D (theta E m) = theta E (theta D m)

/-- Morphisms commuting with all Higgs contractions. -/
structure HiggsHom (E F : IntegrableHiggs k A) where
  hom : E.carrier ⟶ F.carrier
  commutes (D : Tangent k A) (m : E.carrier) :
    hom (E.theta D m) = F.theta D (hom m)

@[ext]
lemma HiggsHom.ext {E F : IntegrableHiggs k A}
    (f g : HiggsHom k A E F) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (IntegrableHiggs k A) where
  Hom := HiggsHom k A
  id E :=
    { hom := 𝟙 E.carrier
      commutes := by intros; rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by
        intro D m
        exact congrArg g.hom (f.commutes D m) |>.trans
          (g.commutes D (f.hom m)) }
  id_comp f := by apply HiggsHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply HiggsHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply HiggsHom.ext; exact Category.assoc f.hom g.hom h.hom

/-- An integrable connection over the affine algebra `A`. -/
structure IntegrableConnection where
  carrier : ModuleCat.{u} A
  nabla : Tangent k A →ₗ[A] Module.End k carrier
  leibniz (D : Tangent k A) (a : A) (m : carrier) :
    nabla D (a • m) = a • nabla D m + D a • m
  flat (D E : Tangent k A) (m : carrier) :
    nabla ⁅D, E⁆ m = nabla D (nabla E m) - nabla E (nabla D m)

/-- Horizontal morphisms of affine connections. -/
structure ConnectionHom (E F : IntegrableConnection k A) where
  hom : E.carrier ⟶ F.carrier
  horizontal (D : Tangent k A) (m : E.carrier) :
    hom (E.nabla D m) = F.nabla D (hom m)

@[ext]
lemma ConnectionHom.ext {E F : IntegrableConnection k A}
    (f g : ConnectionHom k A E F) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (IntegrableConnection k A) where
  Hom := ConnectionHom k A
  id E :=
    { hom := 𝟙 E.carrier
      horizontal := by intros; rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      horizontal := by
        intro D m
        exact congrArg g.hom (f.horizontal D m) |>.trans
          (g.horizontal D (f.hom m)) }
  id_comp f := by apply ConnectionHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply ConnectionHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply ConnectionHom.ext; exact Category.assoc f.hom g.hom h.hom

end AffineObject

namespace AffineFrobeniusLift

variable (k : Type u) (A : Type u) (p : ℕ)
variable [Field k] [CommRing A] [Algebra k A]
variable [CharP k p] [Fact p.Prime]

/-- Frobenius extension of scalars, in mathlib's standard model. -/
abbrev pullback (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  (ModuleCat.extendScalars (algebraFrobenius k A p)).obj M

/-- The affine tangent module, bundled as a `ModuleCat` object. -/
abbrev tangentModule :=
  ModuleCat.of A (Tangent k A)

/-- Pull an individual Higgs contraction through Frobenius extension of
scalars. -/
def pulledEnd (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) : Module.End A (pullback k A p E.carrier) :=
  ((ModuleCat.extendScalars (algebraFrobenius k A p)).map
    (ModuleCat.ofHom (E.theta D))).hom

@[simp]
lemma pulledEnd_tmul (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (a : A) (m : E.carrier) :
    pulledEnd k A p E D
        (StandardFrobeniusPullback.tmul k A E.carrier p a m) =
      StandardFrobeniusPullback.tmul k A E.carrier p a (E.theta D m) :=
  rfl

/-- The balancing relation in the standard Frobenius extension of
scalars, stated without exposing mathlib's restriction-of-scalars wrapper. -/
lemma tmul_smul (M : ModuleCat.{u} A) (a r : A) (m : M) :
    StandardFrobeniusPullback.tmul k A M p a (r • m) =
      algebraFrobenius k A p r •
        StandardFrobeniusPullback.tmul k A M p a m := by
  exact StandardFrobeniusPullback.tmul_smul k A M p a r m

/-- The Frobenius-semilinear map from tangent vectors to pulled-back Higgs
endomorphisms, expressed as a morphism into a restriction of scalars. -/
def thetaUnit (E : AffineObject.IntegrableHiggs k A) :
    tangentModule k A ⟶
      (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
        (ModuleCat.of A (Module.End A (pullback k A p E.carrier))) :=
  ModuleCat.ofHom (Y :=
      (ModuleCat.restrictScalars (algebraFrobenius k A p)).obj
        (ModuleCat.of A (Module.End A (pullback k A p E.carrier))))
    { toFun := pulledEnd k A p E
      map_add' := by
        intro D D'
        change pulledEnd k A p E (D + D') =
          pulledEnd k A p E D + pulledEnd k A p E D'
        have h : ModuleCat.ofHom (pulledEnd k A p E (D + D')) =
            ModuleCat.ofHom
              (pulledEnd k A p E D + pulledEnd k A p E D') := by
          apply ModuleCat.ExtendScalars.hom_ext
          intro m
          change pulledEnd k A p E (D + D')
              (StandardFrobeniusPullback.tmul k A E.carrier p 1 m) =
            (pulledEnd k A p E D + pulledEnd k A p E D')
              (StandardFrobeniusPullback.tmul k A E.carrier p 1 m)
          rw [pulledEnd_tmul, LinearMap.add_apply, pulledEnd_tmul,
            pulledEnd_tmul, map_add, LinearMap.add_apply,
            StandardFrobeniusPullback.tmul_add]
        exact congrArg ModuleCat.Hom.hom h
      map_smul' := by
        intro r D
        change pulledEnd k A p E (r • D) =
          algebraFrobenius k A p r • pulledEnd k A p E D
        have h : ModuleCat.ofHom (pulledEnd k A p E (r • D)) =
            ModuleCat.ofHom
              (algebraFrobenius k A p r • pulledEnd k A p E D) := by
          apply ModuleCat.ExtendScalars.hom_ext
          intro m
          change pulledEnd k A p E (r • D)
              (StandardFrobeniusPullback.tmul k A E.carrier p 1 m) =
            (algebraFrobenius k A p r • pulledEnd k A p E D)
              (StandardFrobeniusPullback.tmul k A E.carrier p 1 m)
          rw [pulledEnd_tmul, LinearMap.smul_apply, pulledEnd_tmul,
            map_smul, LinearMap.smul_apply]
          exact tmul_smul k A p E.carrier 1 r (E.theta D m)
        exact congrArg ModuleCat.Hom.hom h }

/-- Pulled-back Higgs action
`F⁺T_A → End_A(F⁺E)`, obtained from `thetaUnit` by the concrete
extension/restriction-of-scalars adjunction. -/
def pullbackThetaHom (E : AffineObject.IntegrableHiggs k A) :
    pullback k A p (tangentModule k A) ⟶
      ModuleCat.of A (Module.End A (pullback k A p E.carrier)) :=
  (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
    (algebraFrobenius k A p)).symm (thetaUnit k A p E)

/-- The same pulled-back Higgs action as an `A`-linear map. -/
abbrev pullbackTheta (E : AffineObject.IntegrableHiggs k A) :
    pullback k A p (tangentModule k A) →ₗ[A]
      Module.End A (pullback k A p E.carrier) :=
  (pullbackThetaHom k A p E).hom

@[simp]
lemma pullbackTheta_tmul (E : AffineObject.IntegrableHiggs k A)
    (a : A) (D : Tangent k A) :
    pullbackTheta k A p E
        (StandardFrobeniusPullback.tmul k A (Tangent k A) p a D) =
      a • pulledEnd k A p E D := by
  rfl

/-- Pulled-back Higgs contractions commute. -/
lemma pulledEnd_commutes (E : AffineObject.IntegrableHiggs k A)
    (D D' : Tangent k A) (x : pullback k A p E.carrier) :
    pulledEnd k A p E D (pulledEnd k A p E D' x) =
      pulledEnd k A p E D' (pulledEnd k A p E D x) := by
  have h : ModuleCat.ofHom
        ((pulledEnd k A p E D).comp (pulledEnd k A p E D')) =
      ModuleCat.ofHom
        ((pulledEnd k A p E D').comp (pulledEnd k A p E D)) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change pulledEnd k A p E D
        (pulledEnd k A p E D'
          (StandardFrobeniusPullback.tmul k A E.carrier p 1 m)) =
      pulledEnd k A p E D'
        (pulledEnd k A p E D
          (StandardFrobeniusPullback.tmul k A E.carrier p 1 m))
    rw [pulledEnd_tmul, pulledEnd_tmul, pulledEnd_tmul, pulledEnd_tmul,
      E.integrable]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- A pulled-back constant Higgs contraction commutes with the canonical
Cartier connection. -/
lemma canonicalNabla_pulledEnd (E : AffineObject.IntegrableHiggs k A)
    (D V : Tangent k A) (x : pullback k A p E.carrier) :
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
        (pulledEnd k A p E V x) =
      pulledEnd k A p E V
        (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pulledEnd k A p E V (0 : pullback k A p E.carrier)) =
        pulledEnd k A p E V
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (0 : pullback k A p E.carrier))
      simp only [map_zero]
  | tmul a m =>
      let a' : A := a
      let m' : E.carrier := m
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pulledEnd k A p E V
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m')) =
        pulledEnd k A p E V
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m'))
      rw [pulledEnd_tmul, StandardFrobeniusPullback.canonicalNabla_tmul,
        StandardFrobeniusPullback.canonicalNabla_tmul, pulledEnd_tmul]
  | add x y hx hy =>
      let x' : pullback k A p E.carrier := x
      let y' : pullback k A p E.carrier := y
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pulledEnd k A p E V (x' + y')) =
        pulledEnd k A p E V
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (x' + y'))
      rw [map_add, map_add, map_add, map_add, hx, hy]

/-- A constant pulled-back contraction commutes with the action of every
element of the pulled-back tangent module. -/
lemma pulledEnd_pullbackTheta_commutes
    (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (q : pullback k A p (tangentModule k A))
    (x : pullback k A p E.carrier) :
    pulledEnd k A p E D (pullbackTheta k A p E q x) =
      pullbackTheta k A p E q (pulledEnd k A p E D x) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change pulledEnd k A p E D
          (pullbackTheta k A p E
            (0 : pullback k A p (tangentModule k A)) x) =
        pullbackTheta k A p E
          (0 : pullback k A p (tangentModule k A))
          (pulledEnd k A p E D x)
      simp only [map_zero, LinearMap.zero_apply]
  | tmul a V =>
      let a' : A := a
      let V' : Tangent k A := V
      change pulledEnd k A p E D
          (pullbackTheta k A p E
            (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' V') x) =
        pullbackTheta k A p E
          (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' V')
          (pulledEnd k A p E D x)
      rw [pullbackTheta_tmul, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul]
      exact congrArg (fun y ↦ a' • y) (pulledEnd_commutes k A p E D V' x)
  | add q q' hq hq' =>
      let q₁ : pullback k A p (tangentModule k A) := q
      let q₂ : pullback k A p (tangentModule k A) := q'
      change pulledEnd k A p E D
          (pullbackTheta k A p E (q₁ + q₂) x) =
        pullbackTheta k A p E (q₁ + q₂) (pulledEnd k A p E D x)
      simp only [map_add, LinearMap.add_apply]
      rw [hq, hq']

/-- The pulled-back Higgs action is integrable. -/
lemma pullbackTheta_commutes (E : AffineObject.IntegrableHiggs k A)
    (q q' : pullback k A p (tangentModule k A))
    (x : pullback k A p E.carrier) :
    pullbackTheta k A p E q (pullbackTheta k A p E q' x) =
      pullbackTheta k A p E q' (pullbackTheta k A p E q x) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change pullbackTheta k A p E
          (0 : pullback k A p (tangentModule k A))
          (pullbackTheta k A p E q' x) =
        pullbackTheta k A p E q'
          (pullbackTheta k A p E
            (0 : pullback k A p (tangentModule k A)) x)
      simp only [map_zero, LinearMap.zero_apply]
  | tmul a D =>
      let a' : A := a
      let D' : Tangent k A := D
      change pullbackTheta k A p E
          (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D')
          (pullbackTheta k A p E q' x) =
        pullbackTheta k A p E q'
          (pullbackTheta k A p E
            (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D') x)
      rw [pullbackTheta_tmul, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul]
      exact congrArg (fun y ↦ a' • y)
        (pulledEnd_pullbackTheta_commutes k A p E D' q' x)
  | add q₁ q₂ h₁ h₂ =>
      let q₁' : pullback k A p (tangentModule k A) := q₁
      let q₂' : pullback k A p (tangentModule k A) := q₂
      change pullbackTheta k A p E (q₁' + q₂')
          (pullbackTheta k A p E q' x) =
        pullbackTheta k A p E q'
          (pullbackTheta k A p E (q₁' + q₂') x)
      simp only [map_add, LinearMap.add_apply]
      rw [h₁, h₂]

/-- Covariant differentiation of the pulled-back Higgs action differentiates
only its pulled-back tangent coefficient. -/
lemma canonicalNabla_pullbackTheta
    (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (q : pullback k A p (tangentModule k A))
    (x : pullback k A p E.carrier) :
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
        (pullbackTheta k A p E q x) =
      pullbackTheta k A p E
          (StandardFrobeniusPullback.canonicalNabla
            k A (Tangent k A) p D q) x +
        pullbackTheta k A p E q
          (StandardFrobeniusPullback.canonicalNabla
            k A E.carrier p D x) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pullbackTheta k A p E
            (0 : pullback k A p (tangentModule k A)) x) =
        pullbackTheta k A p E
            (StandardFrobeniusPullback.canonicalNabla
              k A (Tangent k A) p D
                (0 : pullback k A p (tangentModule k A))) x +
          pullbackTheta k A p E
            (0 : pullback k A p (tangentModule k A))
            (StandardFrobeniusPullback.canonicalNabla
              k A E.carrier p D x)
      simp only [map_zero, LinearMap.zero_apply, add_zero]
  | tmul a V =>
      let a' : A := a
      let V' : Tangent k A := V
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pullbackTheta k A p E
            (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' V') x) =
        pullbackTheta k A p E
            (StandardFrobeniusPullback.canonicalNabla
              k A (Tangent k A) p D
                (StandardFrobeniusPullback.tmul
                  k A (Tangent k A) p a' V')) x +
          pullbackTheta k A p E
            (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' V')
            (StandardFrobeniusPullback.canonicalNabla
              k A E.carrier p D x)
      rw [pullbackTheta_tmul, LinearMap.smul_apply]
      have hleib := (StandardFrobeniusPullback.canonicalConnection
        k A E.carrier p).leibniz D a' (pulledEnd k A p E V' x)
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (a' • pulledEnd k A p E V' x) =
        a' • StandardFrobeniusPullback.canonicalNabla
            k A E.carrier p D (pulledEnd k A p E V' x) +
          D a' • pulledEnd k A p E V' x at hleib
      rw [hleib,
        StandardFrobeniusPullback.canonicalNabla_tmul,
        pullbackTheta_tmul]
      simp only [LinearMap.smul_apply]
      rw [canonicalNabla_pulledEnd]
      abel
  | add q₁ q₂ h₁ h₂ =>
      let q₁' : pullback k A p (tangentModule k A) := q₁
      let q₂' : pullback k A p (tangentModule k A) := q₂
      change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
          (pullbackTheta k A p E (q₁' + q₂') x) =
        pullbackTheta k A p E
            (StandardFrobeniusPullback.canonicalNabla
              k A (Tangent k A) p D (q₁' + q₂')) x +
          pullbackTheta k A p E (q₁' + q₂')
            (StandardFrobeniusPullback.canonicalNabla
              k A E.carrier p D x)
      simp only [map_add, LinearMap.add_apply]
      rw [h₁, h₂]
      abel

/-- The part of a Frobenius lift used by the affine LSZ formula: the dual
of the divided differential `d F̃ / p`.  Its closedness is the identity
obtained from `d² = 0`; unlike the old interface, it is independent of a
Higgs object. -/
structure DividedDifferential where
  zeta : Tangent k A →ₗ[A] pullback k A p (tangentModule k A)
  closed (D E : Tangent k A) :
    zeta ⁅D, E⁆ =
      StandardFrobeniusPullback.canonicalNabla
          k A (Tangent k A) p D (zeta E) -
        StandardFrobeniusPullback.canonicalNabla
          k A (Tangent k A) p E (zeta D)

namespace DividedDifferential

variable (Z : DividedDifferential k A p)

/-- Forget `A`-linearity of an endomorphism while retaining `A`-linearity
in the endomorphism parameter. -/
def restrictEnd (P : ModuleCat.{u} A) :
    Module.End A P →ₗ[A] Module.End k P where
  toFun f := f.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Higgs correction `F⁺θ ∘ (d F̃/p)`. -/
def correction (E : AffineObject.IntegrableHiggs k A) :
    Tangent k A →ₗ[A] Module.End k (pullback k A p E.carrier) :=
  (restrictEnd k A (pullback k A p E.carrier)).comp
    ((pullbackTheta k A p E).comp Z.zeta)

@[simp]
lemma correction_apply (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (x : pullback k A p E.carrier) :
    correction k A p Z E D x =
      pullbackTheta k A p E (DividedDifferential.zeta Z D) x := rfl

lemma correction_smul (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (a : A) (x : pullback k A p E.carrier) :
    correction k A p Z E D (a • x) =
      a • correction k A p Z E D x := by
  change pullbackTheta k A p E (DividedDifferential.zeta Z D) (a • x) =
    a • pullbackTheta k A p E (DividedDifferential.zeta Z D) x
  exact map_smul
    (pullbackTheta k A p E (DividedDifferential.zeta Z D)) a x

/-- The LSZ covariant derivative
`∇ᶜᵃⁿ + (F⁺θ) ∘ (d F̃/p)`. -/
def nabla (E : AffineObject.IntegrableHiggs k A) :
    Tangent k A →ₗ[A] Module.End k (pullback k A p E.carrier) :=
  StandardFrobeniusPullback.canonicalNabla k A E.carrier p +
    correction k A p Z E

@[simp]
lemma nabla_apply (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (x : pullback k A p E.carrier) :
    nabla k A p Z E D x =
      StandardFrobeniusPullback.canonicalNabla k A E.carrier p D x +
        pullbackTheta k A p E (DividedDifferential.zeta Z D) x := rfl

/-- The corrected operator satisfies the connection Leibniz rule. -/
lemma nabla_leibniz (E : AffineObject.IntegrableHiggs k A)
    (D : Tangent k A) (a : A) (x : pullback k A p E.carrier) :
    nabla k A p Z E D (a • x) =
      a • nabla k A p Z E D x + D a • x := by
  simp only [nabla_apply]
  have hcan := (StandardFrobeniusPullback.canonicalConnection
    k A E.carrier p).leibniz D a x
  change StandardFrobeniusPullback.canonicalNabla k A E.carrier p D (a • x) =
    a • StandardFrobeniusPullback.canonicalNabla k A E.carrier p D x +
      D a • x at hcan
  rw [hcan, map_smul]
  change a • StandardFrobeniusPullback.canonicalNabla
        k A E.carrier p D x + D a • x +
      a • pullbackTheta k A p E (DividedDifferential.zeta Z D) x =
    a • (StandardFrobeniusPullback.canonicalNabla
        k A E.carrier p D x +
      pullbackTheta k A p E (DividedDifferential.zeta Z D) x) + D a • x
  rw [smul_add]
  abel

/-- The corrected operator is flat. -/
lemma nabla_flat (E : AffineObject.IntegrableHiggs k A)
    (D E' : Tangent k A) (x : pullback k A p E.carrier) :
    nabla k A p Z E ⁅D, E'⁆ x =
      nabla k A p Z E D (nabla k A p Z E E' x) -
        nabla k A p Z E E' (nabla k A p Z E D x) := by
  simp only [nabla_apply, map_add]
  have hcan := (StandardFrobeniusPullback.canonicalConnection
    k A E.carrier p).flat D E' x
  change StandardFrobeniusPullback.canonicalNabla k A E.carrier p ⁅D, E'⁆ x =
    StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
        (StandardFrobeniusPullback.canonicalNabla k A E.carrier p E' x) -
      StandardFrobeniusPullback.canonicalNabla k A E.carrier p E'
        (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D x) at hcan
  rw [hcan,
    canonicalNabla_pullbackTheta k A p E D
      (DividedDifferential.zeta Z E') x,
    canonicalNabla_pullbackTheta k A p E E'
      (DividedDifferential.zeta Z D) x,
    pullbackTheta_commutes k A p E
      (DividedDifferential.zeta Z D)
      (DividedDifferential.zeta Z E') x]
  have hz := congrArg
    (fun q : pullback k A p (tangentModule k A) ↦
      pullbackTheta k A p E q x) (DividedDifferential.closed Z D E')
  simp only [map_sub, LinearMap.sub_apply] at hz
  rw [hz]
  abel

/-- A fixed divided Frobenius lift sends every unrestricted integrable
Higgs module to an integrable connection. -/
def connection (E : AffineObject.IntegrableHiggs k A) :
    AffineObject.IntegrableConnection k A where
  carrier := pullback k A p E.carrier
  nabla := nabla k A p Z E
  leibniz := nabla_leibniz k A p Z E
  flat := nabla_flat k A p Z E

/-- Frobenius pullback of a Higgs morphism. -/
def pullbackMap {E G : AffineObject.IntegrableHiggs k A} (f : E ⟶ G) :
    pullback k A p E.carrier ⟶ pullback k A p G.carrier :=
  (ModuleCat.extendScalars (algebraFrobenius k A p)).map f.hom

@[simp]
lemma pullbackMap_tmul {E G : AffineObject.IntegrableHiggs k A}
    (f : E ⟶ G) (a : A) (m : E.carrier) :
    pullbackMap k A p f
        (StandardFrobeniusPullback.tmul k A E.carrier p a m) =
      StandardFrobeniusPullback.tmul k A G.carrier p a (f.hom m) := rfl

/-- Pulled-back Higgs contractions are natural in the Higgs module. -/
lemma pullbackMap_pulledEnd {E G : AffineObject.IntegrableHiggs k A}
    (f : E ⟶ G) (D : Tangent k A)
    (x : pullback k A p E.carrier) :
    pullbackMap k A p f (pulledEnd k A p E D x) =
      pulledEnd k A p G D (pullbackMap k A p f x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change pullbackMap k A p f
          (pulledEnd k A p E D (0 : pullback k A p E.carrier)) =
        pulledEnd k A p G D
          (pullbackMap k A p f (0 : pullback k A p E.carrier))
      simp only [map_zero]
  | tmul a m =>
      let a' : A := a
      let m' : E.carrier := m
      change pullbackMap k A p f
          (pulledEnd k A p E D
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m')) =
        pulledEnd k A p G D
          (pullbackMap k A p f
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m'))
      rw [pulledEnd_tmul, pullbackMap_tmul, pullbackMap_tmul,
        pulledEnd_tmul, f.commutes]
  | add x y hx hy =>
      let x' : pullback k A p E.carrier := x
      let y' : pullback k A p E.carrier := y
      change pullbackMap k A p f
          (pulledEnd k A p E D (x' + y')) =
        pulledEnd k A p G D (pullbackMap k A p f (x' + y'))
      simp only [map_add]
      simpa [x', y'] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- The canonical Cartier connection is natural under Frobenius pullback. -/
lemma pullbackMap_canonicalNabla
    {E G : AffineObject.IntegrableHiggs k A} (f : E ⟶ G)
    (D : Tangent k A) (x : pullback k A p E.carrier) :
    pullbackMap k A p f
        (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D x) =
      StandardFrobeniusPullback.canonicalNabla k A G.carrier p D
        (pullbackMap k A p f x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change pullbackMap k A p f
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (0 : pullback k A p E.carrier)) =
        StandardFrobeniusPullback.canonicalNabla k A G.carrier p D
          (pullbackMap k A p f (0 : pullback k A p E.carrier))
      simp only [map_zero]
  | tmul a m =>
      let a' : A := a
      let m' : E.carrier := m
      change pullbackMap k A p f
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m')) =
        StandardFrobeniusPullback.canonicalNabla k A G.carrier p D
          (pullbackMap k A p f
            (StandardFrobeniusPullback.tmul k A E.carrier p a' m'))
      rw [StandardFrobeniusPullback.canonicalNabla_tmul,
        pullbackMap_tmul, pullbackMap_tmul,
        StandardFrobeniusPullback.canonicalNabla_tmul]
  | add x y hx hy =>
      let x' : pullback k A p E.carrier := x
      let y' : pullback k A p E.carrier := y
      change pullbackMap k A p f
          (StandardFrobeniusPullback.canonicalNabla k A E.carrier p D
            (x' + y')) =
        StandardFrobeniusPullback.canonicalNabla k A G.carrier p D
          (pullbackMap k A p f (x' + y'))
      simp only [map_add]
      simpa [x', y'] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- The complete pulled-back Higgs action is natural. -/
lemma pullbackMap_pullbackTheta
    {E G : AffineObject.IntegrableHiggs k A} (f : E ⟶ G)
    (q : pullback k A p (tangentModule k A))
    (x : pullback k A p E.carrier) :
    pullbackMap k A p f (pullbackTheta k A p E q x) =
      pullbackTheta k A p G q (pullbackMap k A p f x) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change pullbackMap k A p f
          (pullbackTheta k A p E
            (0 : pullback k A p (tangentModule k A)) x) =
        pullbackTheta k A p G
          (0 : pullback k A p (tangentModule k A))
          (pullbackMap k A p f x)
      simp only [map_zero, LinearMap.zero_apply]
  | tmul a D =>
      let a' : A := a
      let D' : Tangent k A := D
      change pullbackMap k A p f
          (pullbackTheta k A p E
            (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D') x) =
        pullbackTheta k A p G
          (StandardFrobeniusPullback.tmul k A (Tangent k A) p a' D')
          (pullbackMap k A p f x)
      rw [pullbackTheta_tmul, LinearMap.smul_apply, map_smul,
        pullbackTheta_tmul, LinearMap.smul_apply,
        pullbackMap_pulledEnd]
  | add q q' hq hq' =>
      let q₁ : pullback k A p (tangentModule k A) := q
      let q₂ : pullback k A p (tangentModule k A) := q'
      change pullbackMap k A p f
          (pullbackTheta k A p E (q₁ + q₂) x) =
        pullbackTheta k A p G (q₁ + q₂) (pullbackMap k A p f x)
      simp only [map_add, LinearMap.add_apply]
      simpa [q₁, q₂] using congrArg₂ (fun a b ↦ a + b) hq hq'

/-- The LSZ covariant derivative is natural in the Higgs object. -/
lemma nabla_natural {E G : AffineObject.IntegrableHiggs k A}
    (f : E ⟶ G) (D : Tangent k A) (x : pullback k A p E.carrier) :
    pullbackMap k A p f (nabla k A p Z E D x) =
      nabla k A p Z G D (pullbackMap k A p f x) := by
  simp only [nabla_apply, map_add]
  rw [pullbackMap_canonicalNabla, pullbackMap_pullbackTheta]

/-- Morphism part of the affine LSZ transform. -/
def map {E G : AffineObject.IntegrableHiggs k A} (f : E ⟶ G) :
    connection k A p Z E ⟶ connection k A p Z G where
  hom := pullbackMap k A p f
  horizontal := nabla_natural k A p Z f

/-- The affine LSZ functor attached to one divided Frobenius lift. -/
def functor :
    AffineObject.IntegrableHiggs k A ⥤
      AffineObject.IntegrableConnection k A where
  obj := connection k A p Z
  map := map k A p Z
  map_id E := by
    apply AffineObject.ConnectionHom.ext
    exact (ModuleCat.extendScalars
      (algebraFrobenius k A p)).map_id E.carrier
  map_comp f g := by
    apply AffineObject.ConnectionHom.ext
    exact (ModuleCat.extendScalars
      (algebraFrobenius k A p)).map_comp f.hom g.hom

end DividedDifferential

end AffineFrobeniusLift

end

end LSZ
