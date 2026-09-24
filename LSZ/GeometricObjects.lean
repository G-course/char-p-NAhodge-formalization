import LSZ.ConnectionTensor
import LSZ.TangentSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Higgs modules and modules with integrable connection

Both structures are defined over an arbitrary field.  Their operators are
genuine morphisms of sheaves:

* a Higgs field is an `O_X`-linear morphism `T_X tensor E ⟶ E`;
* a connection is an additive morphism `a(T_X tensor_Z M) ⟶ M`.

The familiar contracted operators on sections are derived from these
morphisms.  Thus compatibility with restriction is a theorem, not repeated
input data.  Characteristic, Frobenius and nilpotence do not occur here.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- An integrable Higgs module on `X`, represented by the sheaf morphism
`T_X tensor E ⟶ E`. -/
structure IntegrableHiggs where
  carrier : X.scheme.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  thetaHom : higgsTensor X carrier ⟶ carrier
  integrable_tmul (U : X.scheme.Opens) (D E : X.VectorField U)
      (m : Γ(carrier, U)) :
    thetaHom.app U
        (higgsTmul X carrier U D
          (thetaHom.app U (higgsTmul X carrier U E m))) =
      thetaHom.app U
        (higgsTmul X carrier U E
          (thetaHom.app U (higgsTmul X carrier U D m)))

namespace IntegrableHiggs

variable {X}

/-- Contraction of a Higgs sheaf morphism with one explicit vector field. -/
noncomputable def thetaEnd (E : X.IntegrableHiggs)
    (U : X.scheme.Opens) (D : X.VectorField U) :
    Module.End Γ(X.scheme, U) Γ(E.carrier, U) where
  toFun m := E.thetaHom.app U (higgsTmul X E.carrier U D m)
  map_add' m n := by
    rw [higgsTmul_add_right]
    exact map_add (E.thetaHom.val.app (.op U)).hom _ _
  map_smul' a m := by
    rw [higgsTmul_smul_right]
    let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
    change E.thetaHom.val.app (.op U)
        ((((higgsTensor X E.carrier).val.obj (.op U)).smul a').hom
          (higgsTmul X E.carrier U D m)) =
      ((E.carrier.val.obj (.op U)).smul a').hom
        (E.thetaHom.val.app (.op U) (higgsTmul X E.carrier U D m))
    exact map_smul (E.thetaHom.val.app (.op U)).hom a' _

/-- The contracted Higgs field, derived from `thetaHom`. -/
noncomputable def theta (E : X.IntegrableHiggs) (U : X.scheme.Opens) :
    X.VectorField U →ₗ[Γ(X.scheme, U)]
      Module.End Γ(X.scheme, U) Γ(E.carrier, U) where
  toFun := E.thetaEnd U
  map_add' D F := by
    ext m
    change E.thetaHom.app U (higgsTmul X E.carrier U (D + F) m) = _
    rw [higgsTmul_add_left]
    exact map_add (E.thetaHom.val.app (.op U)).hom _ _
  map_smul' a D := by
    ext m
    change E.thetaHom.app U (higgsTmul X E.carrier U (a • D) m) = _
    rw [higgsTmul_smul_left]
    let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
    change E.thetaHom.val.app (.op U)
        ((((higgsTensor X E.carrier).val.obj (.op U)).smul a').hom
          (higgsTmul X E.carrier U D m)) =
      ((E.carrier.val.obj (.op U)).smul a').hom
        (E.thetaHom.val.app (.op U) (higgsTmul X E.carrier U D m))
    exact map_smul (E.thetaHom.val.app (.op U)).hom a' _

@[simp]
lemma theta_apply (E : X.IntegrableHiggs) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(E.carrier, U)) :
    E.theta U D m = E.thetaHom.app U (higgsTmul X E.carrier U D m) := rfl

/-- Sectionwise integrability, derived from the sheaf-morphism field. -/
lemma integrable (E : X.IntegrableHiggs) (U : X.scheme.Opens)
    (D F : X.VectorField U) (m : Γ(E.carrier, U)) :
    E.theta U D (E.theta U F m) = E.theta U F (E.theta U D m) :=
  E.integrable_tmul U D F m

/-- Restriction compatibility follows from naturality of the Higgs-field
sheaf morphism. -/
lemma theta_restrict (E : X.IntegrableHiggs)
    {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U) (m : Γ(E.carrier, U)) :
    E.carrier.presheaf.map (homOfLE hVU).op (E.theta U D m) =
      E.theta V (D.restrict hVU)
        (E.carrier.presheaf.map (homOfLE hVU).op m) := by
  have hn := PresheafOfModules.naturality_apply E.thetaHom.val
    (homOfLE hVU).op (higgsTmul X E.carrier U D m)
  change E.carrier.val.map (homOfLE hVU).op
      (E.thetaHom.val.app (.op U) (higgsTmul X E.carrier U D m)) =
    E.thetaHom.val.app (.op V)
      (higgsTmul X E.carrier V (D.restrict hVU)
        (E.carrier.val.map (homOfLE hVU).op m))
  exact hn.symm.trans (congrArg (E.thetaHom.val.app (.op V))
    (higgsTmul_restrict X E.carrier hVU D m))

end IntegrableHiggs

/-- Morphisms of integrable Higgs modules; compatibility is an equality of
sheaf morphisms. -/
structure HiggsHom (E F : X.IntegrableHiggs) where
  hom : E.carrier ⟶ F.carrier
  commutes_hom :
    E.thetaHom ≫ hom = higgsTensorMap X hom ≫ F.thetaHom

namespace HiggsHom

variable {X} {E F G : X.IntegrableHiggs}

/-- Sectionwise form of `commutes_hom`. -/
lemma commutes (f : X.HiggsHom E F) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(E.carrier, U)) :
    f.hom.app U (E.theta U D m) = F.theta U D (f.hom.app U m) := by
  have h := congrArg (fun q ↦ q.app U) f.commutes_hom
  have hm := CategoryTheory.congr_fun h (higgsTmul X E.carrier U D m)
  change f.hom.app U (E.thetaHom.app U (higgsTmul X E.carrier U D m)) =
    F.thetaHom.app U
      ((higgsTensorMap X f.hom).app U (higgsTmul X E.carrier U D m)) at hm
  rw [higgsTensorMap_tmul] at hm
  exact hm

end HiggsHom

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
      commutes_hom := by
        rw [Category.comp_id, higgsTensorMap_id, Category.id_comp] }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes_hom := by
        rw [← Category.assoc, f.commutes_hom, Category.assoc,
          g.commutes_hom, ← Category.assoc, ← higgsTensorMap_comp] }
  id_comp f := by apply HiggsHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply HiggsHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply HiggsHom.ext; exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma HiggsHom.id_hom (E : X.IntegrableHiggs) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma HiggsHom.comp_hom {E F G : X.IntegrableHiggs}
    (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- A module with integrable connection on `X`.  The connection operator is
stored as a morphism of additive sheaves. -/
structure IntegrableConnection where
  carrier : X.scheme.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  nablaHom : connectionTensor X carrier ⟶
    (SheafOfModules.toSheaf X.scheme.ringCatSheaf).obj carrier
  nabla_smul_vectorField (U : X.scheme.Opens) (a : Γ(X.scheme, U))
      (D : X.VectorField U) (m : Γ(carrier, U)) :
    (show Γ(carrier, U) from
      nablaHom.hom.app (.op U) (connectionTmul X carrier U (a • D) m)) =
      a • (show Γ(carrier, U) from
        nablaHom.hom.app (.op U) (connectionTmul X carrier U D m))
  leibniz_tmul (U : X.scheme.Opens) (D : X.VectorField U)
      (a : Γ(X.scheme, U)) (m : Γ(carrier, U)) :
    (show Γ(carrier, U) from
      nablaHom.hom.app (.op U) (connectionTmul X carrier U D (a • m))) =
      a • (show Γ(carrier, U) from
        nablaHom.hom.app (.op U) (connectionTmul X carrier U D m)) +
        D.act a • m
  flat_tmul (U : X.scheme.Opens) (D E : X.VectorField U)
      (m : Γ(carrier, U)) :
    (show Γ(carrier, U) from
      nablaHom.hom.app (.op U) (connectionTmul X carrier U ⁅D, E⁆ m)) =
      (show Γ(carrier, U) from nablaHom.hom.app (.op U)
          (connectionTmul X carrier U D
            (show Γ(carrier, U) from
              nablaHom.hom.app (.op U) (connectionTmul X carrier U E m)))) -
        (show Γ(carrier, U) from nablaHom.hom.app (.op U)
          (connectionTmul X carrier U E
            (show Γ(carrier, U) from
              nablaHom.hom.app (.op U) (connectionTmul X carrier U D m))))

namespace IntegrableConnection

variable {X}

/-- The additive endomorphism obtained by contracting a connection with one
vector field. -/
noncomputable def nablaAdd (C : X.IntegrableConnection)
    (U : X.scheme.Opens) (D : X.VectorField U) :
    Γ(C.carrier, U) →+ Γ(C.carrier, U) where
  toFun m := C.nablaHom.hom.app (.op U) (connectionTmul X C.carrier U D m)
  map_zero' := by
    rw [connectionTmul_zero_right]
    exact map_zero (C.nablaHom.hom.app (.op U)).hom
  map_add' m n := by
    rw [connectionTmul_add_right]
    exact map_add (C.nablaHom.hom.app (.op U)).hom _ _

/-- The contracted connection, derived from `nablaHom`. -/
noncomputable def nabla (C : X.IntegrableConnection) (U : X.scheme.Opens) :
    X.VectorField U →ₗ[Γ(X.scheme, U)] Module.End ℤ Γ(C.carrier, U) where
  toFun D := (C.nablaAdd U D).toIntLinearMap
  map_add' D E := by
    ext m
    change C.nablaHom.hom.app (.op U)
      (connectionTmul X C.carrier U (D + E) m) = _
    rw [connectionTmul_add_left]
    exact map_add (C.nablaHom.hom.app (.op U)).hom _ _
  map_smul' a D := by
    ext m
    exact C.nabla_smul_vectorField U a D m

@[simp]
lemma nabla_apply (C : X.IntegrableConnection) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(C.carrier, U)) :
    C.nabla U D m =
      C.nablaHom.hom.app (.op U) (connectionTmul X C.carrier U D m) := rfl

/-- The usual sectionwise Leibniz rule, derived from `leibniz_tmul`. -/
lemma leibniz (C : X.IntegrableConnection) (U : X.scheme.Opens)
    (D : X.VectorField U) (a : Γ(X.scheme, U))
    (m : Γ(C.carrier, U)) :
    C.nabla U D (a • m) = a • C.nabla U D m + D.act a • m :=
  C.leibniz_tmul U D a m

/-- The usual sectionwise flatness identity, derived from `flat_tmul`. -/
lemma flat (C : X.IntegrableConnection) (U : X.scheme.Opens)
    (D E : X.VectorField U) (m : Γ(C.carrier, U)) :
    C.nabla U ⁅D, E⁆ m =
      C.nabla U D (C.nabla U E m) - C.nabla U E (C.nabla U D m) :=
  C.flat_tmul U D E m

/-- Restriction compatibility follows from naturality of the connection
sheaf morphism. -/
lemma nabla_restrict (C : X.IntegrableConnection)
    {U V : X.scheme.Opens} (hVU : V ≤ U)
    (D : X.VectorField U) (m : Γ(C.carrier, U)) :
    C.carrier.presheaf.map (homOfLE hVU).op (C.nabla U D m) =
      C.nabla V (D.restrict hVU)
        (C.carrier.presheaf.map (homOfLE hVU).op m) := by
  have hn := CategoryTheory.congr_fun
    (C.nablaHom.hom.naturality (homOfLE hVU).op)
    (connectionTmul X C.carrier U D m)
  change C.carrier.val.map (homOfLE hVU).op
      (C.nablaHom.hom.app (.op U) (connectionTmul X C.carrier U D m)) =
    C.nablaHom.hom.app (.op V)
      (connectionTmul X C.carrier V (D.restrict hVU)
        (C.carrier.val.map (homOfLE hVU).op m))
  change C.nablaHom.hom.app (.op V)
      ((connectionTensor X C.carrier).obj.map (homOfLE hVU).op
        (connectionTmul X C.carrier U D m)) =
    C.carrier.val.map (homOfLE hVU).op
      (C.nablaHom.hom.app (.op U)
        (connectionTmul X C.carrier U D m)) at hn
  exact hn.symm.trans (congrArg (C.nablaHom.hom.app (.op V))
    (connectionTmul_restrict X C.carrier hVU D m))

end IntegrableConnection

/-- Horizontal morphisms of modules with integrable connection. -/
structure ConnectionHom (M N : X.IntegrableConnection) where
  hom : M.carrier ⟶ N.carrier
  horizontal_hom :
    M.nablaHom ≫
        (SheafOfModules.toSheaf X.scheme.ringCatSheaf).map hom =
      connectionTensorMap X hom ≫ N.nablaHom

namespace ConnectionHom

variable {X} {M N P : X.IntegrableConnection}

/-- Sectionwise form of `horizontal_hom`. -/
lemma horizontal (f : X.ConnectionHom M N) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(M.carrier, U)) :
    f.hom.app U (M.nabla U D m) = N.nabla U D (f.hom.app U m) := by
  have h := congrArg (fun q ↦ q.hom.app (.op U)) f.horizontal_hom
  have hm := CategoryTheory.congr_fun h (connectionTmul X M.carrier U D m)
  change f.hom.app U
      (M.nablaHom.hom.app (.op U) (connectionTmul X M.carrier U D m)) =
    N.nablaHom.hom.app (.op U)
      ((connectionTensorMap X f.hom).hom.app (.op U)
        (connectionTmul X M.carrier U D m)) at hm
  rw [connectionTensorMap_tmul] at hm
  exact hm

end ConnectionHom

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
      horizontal_hom := by
        have hF := (SheafOfModules.toSheaf
          X.scheme.ringCatSheaf).map_id M.carrier
        have hT := connectionTensorMap_id X M.carrier
        exact (congrArg (fun q ↦ M.nablaHom ≫ q) hF).trans
          ((Category.comp_id M.nablaHom).trans
            ((Category.id_comp M.nablaHom).symm.trans
              (congrArg (fun q ↦ q ≫ M.nablaHom) hT.symm))) }
  comp f g :=
    { hom := f.hom ≫ g.hom
      horizontal_hom := by
        let F := SheafOfModules.toSheaf X.scheme.ringCatSheaf
        have hF := (SheafOfModules.toSheaf
          X.scheme.ringCatSheaf).map_comp f.hom g.hom
        have hT := connectionTensorMap_comp X f.hom g.hom
        exact (congrArg (fun q ↦ _ ≫ q) hF).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q ↦ q ≫ F.map g.hom)
              f.horizontal_hom).trans
              ((Category.assoc _ _ _).trans
                ((congrArg
                  (fun q ↦ connectionTensorMap X f.hom ≫ q)
                  g.horizontal_hom).trans
                  ((Category.assoc _ _ _).symm.trans
                    (congrArg (fun q ↦ q ≫ _) hT.symm)))))) }
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
