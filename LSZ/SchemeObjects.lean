import LSZ.Objects
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# OV/LSZ objects over an arbitrary scheme

Every definition is parametrized by an arbitrary scheme `X`.  In particular,
the definition of a connection on `X` does not mention another scheme and
does not contain an equality identifying two schemes.  A later statement of
the correspondence may instantiate the two independently defined sides as
desired.

Mathlib does not yet bundle the tangent sheaf of a scheme as a restricted
Lie--Rinehart sheaf.  `RestrictedTangentSheaf` records exactly the local data
needed to state the two sides: the anchor on functions, Lie bracket,
restricted `p`-power, and compatibility with restriction maps.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace LSZ

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ}

/-- Restricted tangent-sheaf data on the single scheme `X`.

The anchor sends a tangent vector on `U` to an absolute derivation of
`Γ(U, 𝒪_X)`.  In the intended positive-characteristic application these are
the derivations relative to the chosen constant field; the absolute version
already gives the correct object definitions over the prime field. -/
structure RestrictedTangentSheaf (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) where
  tangent : X.Modules
  tangent_quasicoherent : tangent.IsQuasicoherent
  prime : p.Prime
  characteristic (U : X.Opens) : CharP Γ(X, U) p
  anchor (U : X.Opens) :
    Γ(tangent, U) →ₗ[Γ(X, U)] Derivation ℤ Γ(X, U) Γ(X, U)
  anchor_restrict {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(tangent, V)) (a : Γ(X, V)) :
    X.presheaf.map i.op (anchor V D a) =
      anchor U (tangent.presheaf.map i.op D) (X.presheaf.map i.op a)
  bracket (U : X.Opens) : Γ(tangent, U) → Γ(tangent, U) → Γ(tangent, U)
  bracket_add_left (U : X.Opens) (D E F : Γ(tangent, U)) :
    bracket U (D + E) F = bracket U D F + bracket U E F
  bracket_add_right (U : X.Opens) (D E F : Γ(tangent, U)) :
    bracket U D (E + F) = bracket U D E + bracket U D F
  bracket_skew (U : X.Opens) (D E : Γ(tangent, U)) :
    bracket U D E = -bracket U E D
  bracket_jacobi (U : X.Opens) (D E F : Γ(tangent, U)) :
    bracket U D (bracket U E F) + bracket U E (bracket U F D) +
      bracket U F (bracket U D E) = 0
  bracket_smul_right (U : X.Opens) (D E : Γ(tangent, U)) (a : Γ(X, U)) :
    bracket U D (a • E) = a • bracket U D E + anchor U D a • E
  bracket_restrict {U V : X.Opens} (i : U ⟶ V)
      (D E : Γ(tangent, V)) :
    tangent.presheaf.map i.op (bracket V D E) =
      bracket U (tangent.presheaf.map i.op D) (tangent.presheaf.map i.op E)
  anchor_bracket (U : X.Opens) (D E : Γ(tangent, U)) (a : Γ(X, U)) :
    anchor U (bracket U D E) a =
      anchor U D (anchor U E a) - anchor U E (anchor U D a)
  pPow (U : X.Opens) : Γ(tangent, U) → Γ(tangent, U)
  pPow_restrict {U V : X.Opens} (i : U ⟶ V) (D : Γ(tangent, V)) :
    tangent.presheaf.map i.op (pPow V D) =
      pPow U (tangent.presheaf.map i.op D)
  anchor_pPow (U : X.Opens) (D : Γ(tangent, U)) (a : Γ(X, U)) :
    anchor U (pPow U D) a = ((anchor U D : Γ(X, U) → Γ(X, U))^[p]) a

namespace SchemeObject

section Higgs

/-- A quasi-coherent integrable Higgs object on `X`, with no nilpotence
assumption.  This is the correct source category when a single global
Frobenius lifting is fixed, since no truncated-exponential gluing is
needed. -/
structure IntegrableHiggs (T : RestrictedTangentSheaf X p) where
  carrier : X.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  theta (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End Γ(X, U) Γ(carrier, U)
  theta_restrict {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(T.tangent, V)) (m : Γ(carrier, V)) :
    carrier.presheaf.map i.op (theta V D m) =
      theta U (T.tangent.presheaf.map i.op D) (carrier.presheaf.map i.op m)
  integrable (U : X.Opens) (D E : Γ(T.tangent, U)) (m : Γ(carrier, U)) :
    theta U D (theta U E m) = theta U E (theta U D m)

/-- A morphism of unrestricted integrable Higgs objects. -/
structure IntegrableHiggsHom {T : RestrictedTangentSheaf X p}
    (E F : IntegrableHiggs T) where
  hom : E.carrier ⟶ F.carrier
  commutes (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(E.carrier, U)) :
    hom.app U (E.theta U D m) = F.theta U D (hom.app U m)

@[ext]
lemma IntegrableHiggsHom.ext {T : RestrictedTangentSheaf X p}
    {E F : IntegrableHiggs T} (f g : IntegrableHiggsHom E F)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (T : RestrictedTangentSheaf X p) : Category (IntegrableHiggs T) where
  Hom := IntegrableHiggsHom
  id E :=
    { hom := 𝟙 E.carrier
      commutes := by
        intro U D m
        rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact (congrArg (g.hom.app U) (f.commutes U D m)).trans
          (g.commutes U D (f.hom.app U m)) }
  id_comp := by
    intro E F f
    apply IntegrableHiggsHom.ext
    exact Category.id_comp f.hom
  comp_id := by
    intro E F f
    apply IntegrableHiggsHom.ext
    exact Category.comp_id f.hom
  assoc := by
    intro E F G H f g h
    apply IntegrableHiggsHom.ext
    exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma IntegrableHiggsHom.id_hom {T : RestrictedTangentSheaf X p}
    (E : IntegrableHiggs T) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma IntegrableHiggsHom.comp_hom {T : RestrictedTangentSheaf X p}
    {E F G : IntegrableHiggs T} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- A quasi-coherent integrable Higgs object on `X`, nilpotent of LSZ level
at most `p - 1`.

For every open `U`, `theta U` is linear in the tangent vector and returns an
`𝒪_X(U)`-linear endomorphism of the coefficient sections.  The restriction
law says these local contractions form a sheaf operation. -/
structure NilpotentHiggs (T : RestrictedTangentSheaf X p) where
  carrier : X.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  theta (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End Γ(X, U) Γ(carrier, U)
  theta_restrict {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(T.tangent, V)) (m : Γ(carrier, V)) :
    carrier.presheaf.map i.op (theta V D m) =
      theta U (T.tangent.presheaf.map i.op D) (carrier.presheaf.map i.op m)
  integrable (U : X.Opens) (D E : Γ(T.tangent, U)) (m : Γ(carrier, U)) :
    theta U D (theta U E m) = theta U E (theta U D m)
  nilpotent (U : X.Opens) :
    IsWordNilpotent p (fun D m => theta U D m)

/-- A morphism of nilpotent Higgs objects: an `𝒪_X`-module morphism commuting
with every local Higgs contraction. -/
structure HiggsHom {T : RestrictedTangentSheaf X p}
    (E F : NilpotentHiggs T) where
  hom : E.carrier ⟶ F.carrier
  commutes (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(E.carrier, U)) :
    hom.app U (E.theta U D m) = F.theta U D (hom.app U m)

@[ext]
lemma HiggsHom.ext {T : RestrictedTangentSheaf X p}
    {E F : NilpotentHiggs T} (f g : HiggsHom E F) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (T : RestrictedTangentSheaf X p) : Category (NilpotentHiggs T) where
  Hom := HiggsHom
  id E :=
    { hom := 𝟙 E.carrier
      commutes := by
        intro U D m
        rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact (congrArg (g.hom.app U) (f.commutes U D m)).trans
          (g.commutes U D (f.hom.app U m)) }
  id_comp := by
    intro E F f
    apply HiggsHom.ext
    exact Category.id_comp f.hom
  comp_id := by
    intro E F f
    apply HiggsHom.ext
    exact Category.comp_id f.hom
  assoc := by
    intro E F G H f g h
    apply HiggsHom.ext
    exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma HiggsHom.id_hom {T : RestrictedTangentSheaf X p} (E : NilpotentHiggs T) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma HiggsHom.comp_hom {T : RestrictedTangentSheaf X p}
    {E F G : NilpotentHiggs T} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Forget the word-nilpotence proof on a Higgs object.  In particular,
this is the inclusion used before applying the unrestricted LSZ functor
attached to one global Frobenius lifting. -/
def nilpotentHiggsForget (T : RestrictedTangentSheaf X p) :
    NilpotentHiggs T ⥤ IntegrableHiggs T where
  obj E :=
    { carrier := E.carrier
      carrier_quasicoherent := E.carrier_quasicoherent
      theta := E.theta
      theta_restrict := E.theta_restrict
      integrable := E.integrable }
  map f :=
    { hom := f.hom
      commutes := f.commutes }
  map_id E := by
    apply IntegrableHiggsHom.ext
    rfl
  map_comp f g := by
    apply IntegrableHiggsHom.ext
    rfl

@[simp]
lemma nilpotentHiggsForget_obj_carrier (T : RestrictedTangentSheaf X p)
    (E : NilpotentHiggs T) :
    ((nilpotentHiggsForget T).obj E).carrier = E.carrier := rfl

@[simp]
lemma nilpotentHiggsForget_map_hom (T : RestrictedTangentSheaf X p)
    {E F : NilpotentHiggs T} (f : E ⟶ F) :
    ((nilpotentHiggsForget T).map f).hom = f.hom := rfl

end Higgs

section Flat

/-- A quasi-coherent module with an integrable connection on `X`.

`nabla U D` is additive in coefficient sections and linear in the tangent
vector.  Its failure to be `𝒪_X(U)`-linear is precisely the Leibniz term
given by the tangent anchor. -/
structure IntegrableConnection (T : RestrictedTangentSheaf X p) where
  carrier : X.Modules
  carrier_quasicoherent : carrier.IsQuasicoherent
  nabla (U : X.Opens) :
    Γ(T.tangent, U) →ₗ[Γ(X, U)] Module.End ℤ Γ(carrier, U)
  nabla_restrict {U V : X.Opens} (i : U ⟶ V)
      (D : Γ(T.tangent, V)) (m : Γ(carrier, V)) :
    carrier.presheaf.map i.op (nabla V D m) =
      nabla U (T.tangent.presheaf.map i.op D) (carrier.presheaf.map i.op m)
  leibniz (U : X.Opens) (D : Γ(T.tangent, U))
      (a : Γ(X, U)) (m : Γ(carrier, U)) :
    nabla U D (a • m) = a • nabla U D m + T.anchor U D a • m
  flat (U : X.Opens) (D E : Γ(T.tangent, U)) (m : Γ(carrier, U)) :
    nabla U (T.bracket U D E) m =
      nabla U D (nabla U E m) - nabla U E (nabla U D m)

/-- A horizontal morphism of unrestricted integrable connections. -/
structure ConnectionHom {T : RestrictedTangentSheaf X p}
    (E F : IntegrableConnection T) where
  hom : E.carrier ⟶ F.carrier
  horizontal (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(E.carrier, U)) :
    hom.app U (E.nabla U D m) = F.nabla U D (hom.app U m)

@[ext]
lemma ConnectionHom.ext {T : RestrictedTangentSheaf X p}
    {E F : IntegrableConnection T} (f g : ConnectionHom E F)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (T : RestrictedTangentSheaf X p) : Category (IntegrableConnection T) where
  Hom := ConnectionHom
  id E :=
    { hom := 𝟙 E.carrier
      horizontal := by
        intro U D m
        rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      horizontal := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact (congrArg (g.hom.app U) (f.horizontal U D m)).trans
          (g.horizontal U D (f.hom.app U m)) }
  id_comp := by
    intro E F f
    apply ConnectionHom.ext
    exact Category.id_comp f.hom
  comp_id := by
    intro E F f
    apply ConnectionHom.ext
    exact Category.comp_id f.hom
  assoc := by
    intro E F G H f g h
    apply ConnectionHom.ext
    exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma ConnectionHom.id_hom {T : RestrictedTangentSheaf X p}
    (E : IntegrableConnection T) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma ConnectionHom.comp_hom {T : RestrictedTangentSheaf X p}
    {E F G : IntegrableConnection T} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The local `p`-curvature operator on an open `U`:
`ψ(D) = ∇(D)^p - ∇(D^[p])`. -/
noncomputable def pCurvature {T : RestrictedTangentSheaf X p}
    (E : IntegrableConnection T) (U : X.Opens)
    (D : Γ(T.tangent, U)) : Module.End ℤ Γ(E.carrier, U) :=
  E.nabla U D ^ p - E.nabla U (T.pPow U D)

/-- The flat side of the OV/LSZ correspondence on `X`: an integrable
connection for which every word of length `p` in local `p`-curvature
operators vanishes. -/
structure NilpotentFlat (T : RestrictedTangentSheaf X p) extends
    IntegrableConnection T where
  nilpotentPCurvature (U : X.Opens) :
    IsWordNilpotent p (fun D m => pCurvature toIntegrableConnection U D m)

/-- A morphism of nilpotent flat objects: an `𝒪_X`-module morphism commuting
with the connection in every tangent direction. -/
structure FlatHom {T : RestrictedTangentSheaf X p}
    (E F : NilpotentFlat T) where
  hom : E.carrier ⟶ F.carrier
  horizontal (U : X.Opens) (D : Γ(T.tangent, U)) (m : Γ(E.carrier, U)) :
    hom.app U (E.nabla U D m) = F.nabla U D (hom.app U m)

@[ext]
lemma FlatHom.ext {T : RestrictedTangentSheaf X p}
    {E F : NilpotentFlat T} (f g : FlatHom E F) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (T : RestrictedTangentSheaf X p) : Category (NilpotentFlat T) where
  Hom := FlatHom
  id E :=
    { hom := 𝟙 E.carrier
      horizontal := by
        intro U D m
        rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      horizontal := by
        intro U D m
        rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
        exact (congrArg (g.hom.app U) (f.horizontal U D m)).trans
          (g.horizontal U D (f.hom.app U m)) }
  id_comp := by
    intro E F f
    apply FlatHom.ext
    exact Category.id_comp f.hom
  comp_id := by
    intro E F f
    apply FlatHom.ext
    exact Category.comp_id f.hom
  assoc := by
    intro E F G H f g h
    apply FlatHom.ext
    exact Category.assoc f.hom g.hom h.hom

@[simp]
lemma FlatHom.id_hom {T : RestrictedTangentSheaf X p} (E : NilpotentFlat T) :
    (𝟙 E : E ⟶ E).hom = 𝟙 E.carrier := rfl

@[simp]
lemma FlatHom.comp_hom {T : RestrictedTangentSheaf X p}
    {E F G : NilpotentFlat T} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Forget nilpotence of `p`-curvature while retaining the underlying
integrable connection.  The `pCurvature` operation itself is already
defined on every object of the target category. -/
def nilpotentFlatForget (T : RestrictedTangentSheaf X p) :
    NilpotentFlat T ⥤ IntegrableConnection T where
  obj E := E.toIntegrableConnection
  map f :=
    { hom := f.hom
      horizontal := f.horizontal }
  map_id E := by
    apply ConnectionHom.ext
    rfl
  map_comp f g := by
    apply ConnectionHom.ext
    rfl

@[simp]
lemma nilpotentFlatForget_obj_carrier (T : RestrictedTangentSheaf X p)
    (E : NilpotentFlat T) :
    ((nilpotentFlatForget T).obj E).carrier = E.carrier := rfl

@[simp]
lemma nilpotentFlatForget_map_hom (T : RestrictedTangentSheaf X p)
    {E F : NilpotentFlat T} (f : E ⟶ F) :
    ((nilpotentFlatForget T).map f).hom = f.hom := rfl

end Flat

end SchemeObject

end LSZ
