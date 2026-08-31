import LSZ.VectorFields
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Higgs modules and modules with integrable connection

Both categories in this file are defined over an arbitrary field.  There is
no characteristic, prime, Frobenius, or nilpotence parameter in either
definition.  Relative vector fields and their Lie bracket are the canonical
ones constructed from `X` in `LSZ.VectorFields`.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- An integrable Higgs module on `X`.

The field `theta U D` is contraction of the Higgs field with the canonical
relative vector field `D`.  Integrability says that all such contractions
commute. -/
structure IntegrableHiggs where
  carrier : X.scheme.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  theta (U : X.scheme.Opens) :
    X.VectorField U →ₗ[Γ(X.scheme, U)] Module.End Γ(X.scheme, U) Γ(carrier, U)
  theta_restrict {U V : X.scheme.Opens} (hVU : V ≤ U)
      (D : X.VectorField U) (m : Γ(carrier, U)) :
    carrier.presheaf.map (homOfLE hVU).op (theta U D m) =
      theta V (D.restrict hVU)
        (carrier.presheaf.map (homOfLE hVU).op m)
  integrable (U : X.scheme.Opens) (D E : X.VectorField U) (m : Γ(carrier, U)) :
    theta U D (theta U E m) = theta U E (theta U D m)

/-- Morphisms of integrable Higgs modules. -/
structure HiggsHom (E F : X.IntegrableHiggs) where
  hom : E.carrier ⟶ F.carrier
  commutes (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(E.carrier, U)) :
    hom.app U (E.theta U D m) = F.theta U D (hom.app U m)

@[ext]
lemma HiggsHom.ext {E F : X.IntegrableHiggs} (f g : X.HiggsHom E F)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category X.IntegrableHiggs where
  Hom := X.HiggsHom
  id E :=
    { hom := 𝟙 E.carrier
      commutes := by intros; rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact congrArg (g.hom.app U) (f.commutes U D m) |>.trans
          (g.commutes U D (f.hom.app U m)) }
  id_comp f := by apply HiggsHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply HiggsHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply HiggsHom.ext; exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma HiggsHom.id_hom (E : X.IntegrableHiggs) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma HiggsHom.comp_hom {E F G : X.IntegrableHiggs} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- A module with integrable connection on `X`.

`nabla` is additive in the module section and `Γ(ᵊa_X,U)`-linear in the
vector field.  The Leibniz rule uses the canonical action `D.act` on
functions; flatness uses the canonical Lie bracket of vector fields. -/
structure IntegrableConnection where
  carrier : X.scheme.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  nabla (U : X.scheme.Opens) :
    X.VectorField U →ₗ[Γ(X.scheme, U)] Module.End ℤ Γ(carrier, U)
  nabla_restrict {U V : X.scheme.Opens} (hVU : V ≤ U)
      (D : X.VectorField U) (m : Γ(carrier, U)) :
    carrier.presheaf.map (homOfLE hVU).op (nabla U D m) =
      nabla V (D.restrict hVU)
        (carrier.presheaf.map (homOfLE hVU).op m)
  leibniz (U : X.scheme.Opens) (D : X.VectorField U)
      (a : Γ(X.scheme, U)) (m : Γ(carrier, U)) :
    nabla U D (a • m) = a • nabla U D m + D.act a • m
  flat (U : X.scheme.Opens) (D E : X.VectorField U) (m : Γ(carrier, U)) :
    nabla U ⁅D, E⁆ m = nabla U D (nabla U E m) - nabla U E (nabla U D m)

/-- Horizontal morphisms of modules with integrable connection. -/
structure ConnectionHom (M N : X.IntegrableConnection) where
  hom : M.carrier ⟶ N.carrier
  horizontal (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M.carrier, U)) :
    hom.app U (M.nabla U D m) = N.nabla U D (hom.app U m)

@[ext]
lemma ConnectionHom.ext {M N : X.IntegrableConnection}
    (f g : X.ConnectionHom M N) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category X.IntegrableConnection where
  Hom := X.ConnectionHom
  id M :=
    { hom := 𝟙 M.carrier
      horizontal := by intros; rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      horizontal := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact congrArg (g.hom.app U) (f.horizontal U D m) |>.trans
          (g.horizontal U D (f.hom.app U m)) }
  id_comp f := by apply ConnectionHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply ConnectionHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply ConnectionHom.ext; exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma ConnectionHom.id_hom (M : X.IntegrableConnection) :
    (𝟙 M : M ⟶ M).hom = 𝟙 M.carrier := rfl

@[simp]
lemma ConnectionHom.comp_hom {M N P : X.IntegrableConnection}
    (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

end


end LSZ.SmoothScheme
