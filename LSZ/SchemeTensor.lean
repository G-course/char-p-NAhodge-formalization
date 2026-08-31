import LSZ.SheafInternalHom
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

open CategoryTheory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

namespace LSZ.SchemeTensor

universe u

noncomputable section

open AlgebraicGeometry

variable (X : Scheme.{u})

/-- Tensor product of two modules on a scheme, inherited from the ringed-space construction. -/
abbrev tensor (M N : X.Modules) : X.Modules :=
  CommRingSheaf.tensorObj X.sheaf M N

/-- Internal Hom of two modules on a scheme, inherited from the ringed-space construction. -/
abbrev internalHom (M N : X.Modules) : X.Modules :=
  CommRingSheaf.internalHom X.sheaf M N

variable {R : CommRingCat.{u}}

section TopOver

variable {T : TopCat.{u}}
  (A : TopCat.Sheaf CommRingCat.{u} T)
  (M N : CommRingSheaf.RingedModules A)

private noncomputable def homFromTopOverApp
    (f : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T))
    (U : (Opens T)ᵒᵖ) : M.val.obj U ⟶ N.val.obj U :=
  f.val.app (op (Over.mk (homOfLE le_top)))

private lemma homFromTopOverApp_naturality
    (f : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T))
    {U V : (Opens T)ᵒᵖ} (q : U ⟶ V) :
    M.val.map q ≫
        (ModuleCat.restrictScalars ((CommRingSheaf.topRingSheaf A).obj.map q).hom).map
          (homFromTopOverApp A M N f V) =
      homFromTopOverApp A M N f U ≫ N.val.map q := by
  let e : Over.mk (homOfLE le_top : V.unop ⟶ (⊤ : Opens T)) ⟶
      Over.mk (homOfLE le_top : U.unop ⟶ (⊤ : Opens T)) :=
    Over.homMk q.unop
  exact f.val.naturality e.op

private noncomputable def homFromTopOverVal
    (f : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T)) : M.val ⟶ N.val where
  app := homFromTopOverApp A M N f
  naturality := homFromTopOverApp_naturality A M N f

noncomputable def homFromTopOver
    (f : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T)) : M ⟶ N where
  val := homFromTopOverVal A M N f

lemma homFromTopOver_over (f : M ⟶ N) :
    homFromTopOver A M N (f.over (⊤ : Opens T)) = f := by
  apply SheafOfModules.hom_ext
  ext U x
  change f.val.app U x = f.val.app U x
  rfl

lemma over_homFromTopOver
    (f : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T)) :
    (homFromTopOver A M N f).over (⊤ : Opens T) = f := by
  apply SheafOfModules.hom_ext
  ext U x
  let W := U.unop
  let C : Over (⊤ : Opens T) := Over.mk (homOfLE le_top : W.left ⟶ ⊤)
  let e : W ⟶ C := Over.homMk (𝟙 W.left)
  have hM : (M.over (⊤ : Opens T)).val.map e.op x = x := by
    change M.val.map (𝟙 (op W.left)) x = x
    exact CategoryTheory.congr_fun (M.val.map_id (op W.left)) x
  have hN : (N.over (⊤ : Opens T)).val.map e.op (f.val.app (op C) x) =
      f.val.app (op C) x := by
    change N.val.map (𝟙 (op W.left)) (f.val.app (op C) x) = _
    exact CategoryTheory.congr_fun (N.val.map_id (op W.left)) _
  have h := PresheafOfModules.naturality_apply f.val e.op x
  rw [hM, hN] at h
  exact h.symm

private noncomputable def topOverHomInvFun
    (f : M ⟶ N) : M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T) :=
  f.over (⊤ : Opens T)

noncomputable def topOverHomEquiv :
    (M.over (⊤ : Opens T) ⟶ N.over (⊤ : Opens T)) ≃ (M ⟶ N) where
  toFun := homFromTopOver A M N
  invFun := topOverHomInvFun A M N
  left_inv := over_homFromTopOver A M N
  right_inv := homFromTopOver_over A M N

end TopOver

section AffineInternalHom

variable {R : CommRingCat.{u}}
  (N : ModuleCat.{u} R) (P : (Spec R).Modules)

private noncomputable def affineInternalHomSource : ModuleCat.{u} R :=
  moduleSpecΓFunctor.obj
    (internalHom (Spec R) (AlgebraicGeometry.tilde N) P)

private noncomputable def affineInternalHomTarget : ModuleCat.{u} R :=
  (ihom N).obj (moduleSpecΓFunctor.obj P)

private noncomputable def affineInternalHomToFun
    (s : affineInternalHomSource N P) : affineInternalHomTarget N P :=
  (AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv N P
    (topOverHomEquiv (Spec R).sheaf (AlgebraicGeometry.tilde N) P s)

private lemma affineInternalHomToFun_add
    (s t : affineInternalHomSource N P) :
    affineInternalHomToFun N P (s + t) =
      affineInternalHomToFun N P s + affineInternalHomToFun N P t := by
  apply ModuleCat.hom_ext
  ext n
  rfl

private lemma affineInternalHomToFun_smul
    (r : R) (s : affineInternalHomSource N P) :
    affineInternalHomToFun N P (r • s) =
      r • affineInternalHomToFun N P s := by
  apply ModuleCat.hom_ext
  ext n
  rfl

noncomputable def affineInternalHomTo :
    moduleSpecΓFunctor.obj
        (internalHom (Spec R) (AlgebraicGeometry.tilde N) P) ⟶
      (ihom N).obj (moduleSpecΓFunctor.obj P) :=
  ModuleCat.ofHom (X := affineInternalHomSource N P)
    (Y := affineInternalHomTarget N P)
    { toFun := affineInternalHomToFun N P
      map_add' := affineInternalHomToFun_add N P
      map_smul' := affineInternalHomToFun_smul N P }

@[simp]
private lemma affineInternalHomTo_apply (s : affineInternalHomSource N P) :
    affineInternalHomTo N P s = affineInternalHomToFun N P s := by
  rfl

lemma affineInternalHomTo_bijective :
    Function.Bijective (affineInternalHomTo N P) := by
  constructor
  · intro s t h
    apply (topOverHomEquiv (Spec R).sheaf (AlgebraicGeometry.tilde N) P).injective
    apply ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv N P).injective
    exact h
  · intro f
    let e₁ := topOverHomEquiv (Spec R).sheaf (AlgebraicGeometry.tilde N) P
    let e₂ := (AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv N P
    refine ⟨e₁.symm (e₂.symm f), ?_⟩
    change e₂ (e₁ (e₁.symm (e₂.symm f))) = f
    exact (congrArg e₂ (e₁.apply_symm_apply (e₂.symm f))).trans
      (e₂.apply_symm_apply f)

noncomputable def affineInternalHomIso :
    moduleSpecΓFunctor.obj
        (internalHom (Spec R) (AlgebraicGeometry.tilde N) P) ≅
      (ihom N).obj (moduleSpecΓFunctor.obj P) :=
  (LinearEquiv.ofBijective (affineInternalHomTo N P).hom
    (affineInternalHomTo_bijective N P)).toModuleIso

@[simp]
lemma affineInternalHomIso_hom :
    (affineInternalHomIso N P).hom = affineInternalHomTo N P := by
  rfl

lemma affineInternalHomTo_naturality {Q : (Spec R).Modules} (g : P ⟶ Q) :
    moduleSpecΓFunctor.map
        (CommRingSheaf.internalHomMap (Spec R).sheaf
          (AlgebraicGeometry.tilde N) g) ≫
      affineInternalHomTo N Q =
    affineInternalHomTo N P ≫
      (ihom N).map (moduleSpecΓFunctor.map g) := by
  apply ModuleCat.hom_ext
  ext s n
  rfl

end AffineInternalHom

section AffineTensor

variable {R : CommRingCat.{u}}
  (M N : ModuleCat.{u} R) (P : (Spec R).Modules)

noncomputable def affineTensorHomEquiv :
    (tensor (Spec R) (AlgebraicGeometry.tilde M)
        (AlgebraicGeometry.tilde N) ⟶ P) ≃
      (AlgebraicGeometry.tilde (M ⊗ N) ⟶ P) :=
  (CommRingSheaf.tensorInternalHomEquiv (Spec R).sheaf
      (AlgebraicGeometry.tilde M) (AlgebraicGeometry.tilde N) P).trans
    (((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv M
      (internalHom (Spec R) (AlgebraicGeometry.tilde N) P)).trans
    (((affineInternalHomIso N P).homToEquiv).trans
    ((((ihom.adjunction N).homEquiv M (moduleSpecΓFunctor.obj P)).symm).trans
    ((((β_ M N).homFromEquiv).symm).trans
      ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv (M ⊗ N) P).symm))))

lemma affineTensorHomEquiv_apply
    (f : tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ P) :
    affineTensorHomEquiv M N P f =
      ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv
        (M ⊗ N) P).symm
        ((β_ M N).hom ≫
          ((ihom.adjunction N).homEquiv M
            (moduleSpecΓFunctor.obj P)).symm
            (((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv M
              (internalHom (Spec R) (AlgebraicGeometry.tilde N) P)
              (CommRingSheaf.tensorInternalHomEquiv (Spec R).sheaf
                (AlgebraicGeometry.tilde M) (AlgebraicGeometry.tilde N) P f)) ≫
              (affineInternalHomIso N P).hom)) := by
  rfl

lemma affineTensorHomEquiv_naturality {Q : (Spec R).Modules}
    (f : tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ P) (g : P ⟶ Q) :
    affineTensorHomEquiv M N Q (f ≫ g) =
      affineTensorHomEquiv M N P f ≫ g := by
  let IHP := internalHom (Spec R) (AlgebraicGeometry.tilde N) P
  let IHQ := internalHom (Spec R) (AlgebraicGeometry.tilde N) Q
  let hg := CommRingSheaf.internalHomMap (Spec R).sheaf
    (AlgebraicGeometry.tilde N) g
  let tP : AlgebraicGeometry.tilde M ⟶ IHP :=
    CommRingSheaf.tensorInternalHomEquiv (Spec R).sheaf
      (AlgebraicGeometry.tilde M) (AlgebraicGeometry.tilde N) P f
  let tQ : AlgebraicGeometry.tilde M ⟶ IHQ :=
    CommRingSheaf.tensorInternalHomEquiv (Spec R).sheaf
      (AlgebraicGeometry.tilde M) (AlgebraicGeometry.tilde N) Q (f ≫ g)
  let aP : M ⟶ moduleSpecΓFunctor.obj IHP :=
    (AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv M IHP tP
  let aQ : M ⟶ moduleSpecΓFunctor.obj IHQ :=
    (AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv M IHQ tQ
  let bP : M ⟶ (ihom N).obj (moduleSpecΓFunctor.obj P) :=
    aP ≫ (affineInternalHomIso N P).hom
  let bQ : M ⟶ (ihom N).obj (moduleSpecΓFunctor.obj Q) :=
    aQ ≫ (affineInternalHomIso N Q).hom
  let dP : N ⊗ M ⟶ moduleSpecΓFunctor.obj P :=
    ((ihom.adjunction N).homEquiv M (moduleSpecΓFunctor.obj P)).symm bP
  let dQ : N ⊗ M ⟶ moduleSpecΓFunctor.obj Q :=
    ((ihom.adjunction N).homEquiv M (moduleSpecΓFunctor.obj Q)).symm bQ
  let eP : M ⊗ N ⟶ moduleSpecΓFunctor.obj P := (β_ M N).hom ≫ dP
  let eQ : M ⊗ N ⟶ moduleSpecΓFunctor.obj Q := (β_ M N).hom ≫ dQ
  have ht : tQ = tP ≫ hg :=
    CommRingSheaf.tensorInternalHomEquiv_naturality_right
      (Spec R).sheaf (AlgebraicGeometry.tilde M)
        (AlgebraicGeometry.tilde N) f g
  have ha : aQ = aP ≫ moduleSpecΓFunctor.map hg := by
    dsimp [aQ, aP]
    rw [ht]
    exact (AlgebraicGeometry.tilde.adjunction
      (R := R)).homEquiv_naturality_right _ _
  have hb : bQ = bP ≫ (ihom N).map (moduleSpecΓFunctor.map g) := by
    dsimp [bQ, bP]
    rw [ha, Category.assoc, affineInternalHomIso_hom,
      affineInternalHomIso_hom,
      affineInternalHomTo_naturality N P g, ← Category.assoc]
  have hd : dQ = dP ≫ moduleSpecΓFunctor.map g := by
    dsimp [dQ, dP]
    rw [hb]
    exact (ihom.adjunction N).homEquiv_naturality_right_symm _ _
  have he : eQ = eP ≫ moduleSpecΓFunctor.map g := by
    dsimp [eQ, eP]
    rw [hd, Category.assoc]
  rw [affineTensorHomEquiv_apply, affineTensorHomEquiv_apply]
  change ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv
      (M ⊗ N) Q).symm eQ =
    ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv
      (M ⊗ N) P).symm eP ≫ g
  rw [he]
  exact (AlgebraicGeometry.tilde.adjunction
    (R := R)).homEquiv_naturality_right_symm _ _

private noncomputable def affineTensorCoyonedaForward
    {Q : (Spec R).Modules}
    (f : AlgebraicGeometry.tilde (M ⊗ N) ⟶ Q) :
    tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ Q :=
  (affineTensorHomEquiv M N Q).symm f

private noncomputable def affineTensorCoyonedaBackward
    {Q : (Spec R).Modules}
    (f : tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ Q) :
    AlgebraicGeometry.tilde (M ⊗ N) ⟶ Q :=
  affineTensorHomEquiv M N Q f

private lemma affineTensorCoyoneda_left_inv
    {Q : (Spec R).Modules}
    (f : AlgebraicGeometry.tilde (M ⊗ N) ⟶ Q) :
    affineTensorCoyonedaBackward M N
      (affineTensorCoyonedaForward M N f) = f :=
  (affineTensorHomEquiv M N Q).apply_symm_apply f

private lemma affineTensorCoyoneda_right_inv
    {Q : (Spec R).Modules}
    (f : tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ Q) :
    affineTensorCoyonedaForward M N
      (affineTensorCoyonedaBackward M N f) = f :=
  (affineTensorHomEquiv M N Q).symm_apply_apply f

private lemma affineTensorCoyoneda_naturality
    {Q S : (Spec R).Modules}
    (f : tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N) ⟶ Q) (g : Q ⟶ S) :
    affineTensorCoyonedaBackward M N (f ≫ g) =
      affineTensorCoyonedaBackward M N f ≫ g :=
  affineTensorHomEquiv_naturality M N Q f g

/-- On an affine scheme, sheaf tensor product agrees with tensor product of modules. -/
noncomputable def affineTensorIso :
    tensor (Spec R) (AlgebraicGeometry.tilde M)
        (AlgebraicGeometry.tilde N) ≅
      AlgebraicGeometry.tilde (M ⊗ N) :=
  (Coyoneda.ext
    (AlgebraicGeometry.tilde (M ⊗ N))
    (tensor (Spec R) (AlgebraicGeometry.tilde M)
      (AlgebraicGeometry.tilde N))
    (affineTensorCoyonedaForward M N)
    (affineTensorCoyonedaBackward M N)
    (affineTensorCoyoneda_left_inv M N)
    (affineTensorCoyoneda_right_inv M N)
    (affineTensorCoyoneda_naturality M N)).symm

end AffineTensor

end

end LSZ.SchemeTensor
