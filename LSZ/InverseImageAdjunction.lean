import LSZ.InverseImagePresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

open CategoryTheory Limits Opposite TopologicalSpace

namespace LSZ.InverseImageAdjunction

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (A : Y.Presheaf CommRingCat.{u})

noncomputable def ringUnit :
    A ⟶ (Opens.map f).op ⋙ LSZ.InverseImagePresheaf.ring f A :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app A

abbrev ringUnit' :
    (A ⋙ forget₂ CommRingCat RingCat) ⟶
      (Opens.map f).op ⋙
        (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight (ringUnit f A) (forget₂ CommRingCat RingCat)

noncomputable def pushforward :
    PresheafOfModules.{u}
        (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward (ringUnit' f A)

private abbrev canonicalIndex (V : (Opens Y)ᵒᵖ) :
    LSZ.InverseImagePresheaf.Index f ((Opens.map f).op.obj V) :=
  CostructuredArrow.mk (𝟙 _)

lemma moduleUnit_eq_cocone
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
        M.presheaf).app V m =
      (LSZ.InverseImagePresheaf.moduleCocone f A M
        ((Opens.map f).op.obj V)).ι.app (canonicalIndex f V) m := by
  change ((Opens.map f).op.lanUnit.app M.presheaf).app V m =
    (((Opens.map f).op.lanUnit.app M.presheaf).app V ≫
      ((Opens.map f).op.lan.obj M.presheaf).map (𝟙 _)) m
  rw [((Opens.map f).op.lan.obj M.presheaf).map_id]
  rfl

lemma ringUnit_eq_cocone (V : (Opens Y)ᵒᵖ) (a : A.obj V) :
    (ringUnit f A).app V a =
      (LSZ.InverseImagePresheaf.commRingCocone f A
        ((Opens.map f).op.obj V)).ι.app (canonicalIndex f V) a := by
  change ((Opens.map f).op.lanUnit.app A).app V a =
    (((Opens.map f).op.lanUnit.app A).app V ≫
      ((Opens.map f).op.lan.obj A).map (𝟙 _)) a
  rw [((Opens.map f).op.lan.obj A).map_id]
  rfl

lemma moduleUnit_smul
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (V : (Opens Y)ᵒᵖ) (a : A.obj V) (m : M.obj V) :
    (show (LSZ.InverseImagePresheaf.module f A M).obj
        ((Opens.map f).op.obj V) from
      ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
        M.presheaf).app V (a • m)) =
      (ringUnit f A).app V a •
        (show (LSZ.InverseImagePresheaf.module f A M).obj
            ((Opens.map f).op.obj V) from
          ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
            M.presheaf).app V m) := by
  rw [moduleUnit_eq_cocone, moduleUnit_eq_cocone, ringUnit_eq_cocone]
  let U := (Opens.map f).op.obj V
  letI (i : LSZ.InverseImagePresheaf.Index f U) :
      Module ((LSZ.InverseImagePresheaf.ringDiagram f A U).obj i)
        ((LSZ.InverseImagePresheaf.moduleDiagram f A M U).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj
        ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
    infer_instance
  exact IsColimit.ι_smul
    (LSZ.InverseImagePresheaf.ringDiagram f A U)
    (LSZ.InverseImagePresheaf.moduleDiagram f A M U)
    (fun e s y ↦ M.map_smul
      (CostructuredArrow.proj (Opens.map f).op U |>.map e) s y)
    (LSZ.InverseImagePresheaf.ringIsColimit f A U)
    (LSZ.InverseImagePresheaf.moduleIsColimit f A M U)
    (canonicalIndex f V) a m

private noncomputable def toUnderlying
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q) :
    M.presheaf ⟶ ((pushforward f A).obj Q).presheaf := by
  exact (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
    M.presheaf Q.presheaf
      ((PresheafOfModules.toPresheaf
        (LSZ.InverseImagePresheaf.ring f A ⋙
          forget₂ CommRingCat RingCat)).map g)

@[simp]
private lemma toUnderlying_apply
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    (toUnderlying f A g).app V m =
      g.app ((Opens.map f).op.obj V)
        (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
          M.presheaf).app V m) := by
  let adj := TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f
  let ug := (PresheafOfModules.toPresheaf
    (LSZ.InverseImagePresheaf.ring f A ⋙
      forget₂ CommRingCat RingCat)).map g
  have h := congr_app (adj.homEquiv_unit (f := ug)) V
  have hm := ConcreteCategory.congr_hom h m
  change (toUnderlying f A g).app V m =
    g.app ((Opens.map f).op.obj V)
      (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
        M.presheaf).app V m) at hm
  exact hm

noncomputable def toPushforward
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q) :
    M ⟶ (pushforward f A).obj Q :=
  PresheafOfModules.homMk (toUnderlying f A g) (fun V a m ↦ by
    rw [toUnderlying_apply, toUnderlying_apply]
    change g.app ((Opens.map f).op.obj V)
        (show (LSZ.InverseImagePresheaf.module f A M).obj
            ((Opens.map f).op.obj V) from
          ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
            M.presheaf).app V (a • m)) =
      (ringUnit f A).app V a •
        g.app ((Opens.map f).op.obj V)
          (show (LSZ.InverseImagePresheaf.module f A M).obj
              ((Opens.map f).op.obj V) from
            ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
              M.presheaf).app V m)
    rw [moduleUnit_smul]
    exact (g.app ((Opens.map f).op.obj V)).hom.map_smul _ _)

private noncomputable def fromUnderlying
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ (pushforward f A).obj Q) :
    (LSZ.InverseImagePresheaf.module f A M).presheaf ⟶ Q.presheaf := by
  exact ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
    M.presheaf Q.presheaf).symm
      ((PresheafOfModules.toPresheaf
        (A ⋙ forget₂ CommRingCat RingCat)).map h)

@[simp]
private lemma fromUnderlying_cocone_apply
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ (pushforward f A).obj Q)
    (U : (Opens X)ᵒᵖ) (j : LSZ.InverseImagePresheaf.Index f U)
    (m : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (fromUnderlying f A h).app U
        ((LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j m) =
      Q.map j.hom (h.app j.left m) := by
  let adj := TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f
  let uh : M.presheaf ⟶
      (TopCat.Presheaf.pushforward Ab.{u} f).obj Q.presheaf := by
    exact (PresheafOfModules.toPresheaf
      (A ⋙ forget₂ CommRingCat RingCat)).map h
  let k : (Opens.map f).op.lan.obj M.presheaf ⟶ Q.presheaf := by
    exact fromUnderlying f A h
  have hfac :
      ((Opens.map f).op.lanUnit.app M.presheaf).app j.left ≫
          k.app ((Opens.map f).op.obj j.left) =
        uh.app j.left := by
    have heq := congr_app
      ((adj.homEquiv M.presheaf Q.presheaf).apply_symm_apply uh) j.left
    rw [adj.homEquiv_unit] at heq
    exact heq
  have hmorph :
      ((Opens.map f).op.lanUnit.app M.presheaf).app j.left ≫
          ((Opens.map f).op.lan.obj M.presheaf).map j.hom ≫ k.app U =
        uh.app j.left ≫ Q.presheaf.map j.hom := by
    rw [k.naturality j.hom, ← Category.assoc, hfac]
  have hm := ConcreteCategory.congr_hom hmorph m
  change (fromUnderlying f A h).app U
      ((LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j m) =
    Q.map j.hom (h.app j.left m) at hm
  exact hm

private lemma ringUnit_map_eq_cocone
    (U : (Opens X)ᵒᵖ) (j : LSZ.InverseImagePresheaf.Index f U)
    (a : A.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (LSZ.InverseImagePresheaf.ring f A).map j.hom
        ((ringUnit f A).app j.left a) =
      (LSZ.InverseImagePresheaf.commRingCocone f A U).ι.app j a := by
  rfl

private lemma cocone_smul
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens X)ᵒᵖ) (j : LSZ.InverseImagePresheaf.Index f U)
    (a : A.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j))
    (m : M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj j)) :
    (show (LSZ.InverseImagePresheaf.module f A M).obj U from
      (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j (a • m)) =
      (show (LSZ.InverseImagePresheaf.ring f A ⋙
          forget₂ CommRingCat RingCat).obj U from
        (LSZ.InverseImagePresheaf.ringCocone f A U).ι.app j a) •
        (show (LSZ.InverseImagePresheaf.module f A M).obj U from
          (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j m) := by
  letI (i : LSZ.InverseImagePresheaf.Index f U) :
      Module ((LSZ.InverseImagePresheaf.ringDiagram f A U).obj i)
        ((LSZ.InverseImagePresheaf.moduleDiagram f A M U).obj i) := by
    change Module
      ((A ⋙ forget₂ CommRingCat RingCat).obj
        ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
    infer_instance
  have hs := IsColimit.ι_smul
    (LSZ.InverseImagePresheaf.ringDiagram f A U)
    (LSZ.InverseImagePresheaf.moduleDiagram f A M U)
    (fun e s y ↦ M.map_smul
      (CostructuredArrow.proj (Opens.map f).op U |>.map e) s y)
    (LSZ.InverseImagePresheaf.ringIsColimit f A U)
    (LSZ.InverseImagePresheaf.moduleIsColimit f A M U) j a m
  change
    (show (LSZ.InverseImagePresheaf.module f A M).obj U from
      (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j (a • m)) =
      (show (LSZ.InverseImagePresheaf.ring f A ⋙
          forget₂ CommRingCat RingCat).obj U from
        (LSZ.InverseImagePresheaf.ringCocone f A U).ι.app j a) •
        (show (LSZ.InverseImagePresheaf.module f A M).obj U from
          (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j m) at hs
  exact hs

noncomputable def fromPushforward
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ (pushforward f A).obj Q) :
    LSZ.InverseImagePresheaf.module f A M ⟶ Q :=
  PresheafOfModules.homMk (fromUnderlying f A h) (fun U r x ↦ by
    letI (i : LSZ.InverseImagePresheaf.Index f U) :
        Module ((LSZ.InverseImagePresheaf.ringDiagram f A U).obj i)
          ((LSZ.InverseImagePresheaf.moduleDiagram f A M U).obj i) := by
      change Module
        ((A ⋙ forget₂ CommRingCat RingCat).obj
          ((CostructuredArrow.proj (Opens.map f).op U).obj i))
        (M.obj ((CostructuredArrow.proj (Opens.map f).op U).obj i))
      infer_instance
    obtain ⟨j, a, m, rfl, rfl⟩ :=
      LSZ.InverseImagePresheaf.jointly_surjective f A M U r x
    let rU : (LSZ.InverseImagePresheaf.ring f A ⋙
        forget₂ CommRingCat RingCat).obj U :=
      (LSZ.InverseImagePresheaf.ringCocone f A U).ι.app j a
    let mU : (LSZ.InverseImagePresheaf.module f A M).obj U :=
      (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j m
    let amU : (LSZ.InverseImagePresheaf.module f A M).obj U :=
      (LSZ.InverseImagePresheaf.moduleCocone f A M U).ι.app j (a • m)
    let aL : A.obj j.left := by exact a
    let mL : M.obj j.left := by exact m
    let sV : (LSZ.InverseImagePresheaf.ring f A).obj
        ((Opens.map f).op.obj j.left) := (ringUnit f A).app j.left aL
    let qV : Q.obj ((Opens.map f).op.obj j.left) := h.app j.left mL
    let sU : (LSZ.InverseImagePresheaf.ring f A).obj U :=
      (LSZ.InverseImagePresheaf.ring f A).map j.hom sV
    let qU : Q.obj U := Q.map j.hom qV
    change (fromUnderlying f A h).app U (rU • mU) =
      rU • (fromUnderlying f A h).app U mU
    have hs : amU = rU • mU := cocone_smul f A M U j a m
    have hh := (h.app j.left).hom.map_smul aL mL
    change (show Q.obj ((Opens.map f).op.obj j.left) from
        h.app j.left (aL • mL)) = sV • qV at hh
    have h₁ : (fromUnderlying f A h).app U (rU • mU) =
        (fromUnderlying f A h).app U amU :=
      congrArg (fun z : (LSZ.InverseImagePresheaf.module f A M).obj U ↦
        (fromUnderlying f A h).app U z) hs.symm
    have h₂ : (fromUnderlying f A h).app U amU =
        Q.map j.hom (h.app j.left (aL • mL)) := by
      have ht := fromUnderlying_cocone_apply f A h U j (a • m)
      change (fromUnderlying f A h).app U amU =
        Q.map j.hom (h.app j.left (aL • mL)) at ht
      exact ht
    have h₃ : Q.map j.hom (h.app j.left (aL • mL)) =
        Q.map j.hom (sV • qV) :=
      congrArg (fun z ↦ Q.map j.hom z) hh
    have hq := Q.map_smul j.hom sV qV
    change Q.map j.hom (sV • qV) = sU • qU at hq
    have hr := ringUnit_map_eq_cocone f A U j a
    change sU = rU at hr
    have hm := fromUnderlying_cocone_apply f A h U j m
    change (fromUnderlying f A h).app U mU = qU at hm
    have h₄ : Q.map j.hom (sV • qV) =
        rU • (fromUnderlying f A h).app U mU :=
      hq.trans (congrArg₂ (fun s q ↦ s • q) hr hm.symm)
    exact h₁.trans (h₂.trans (h₃.trans h₄)))

@[simp]
private lemma toPushforward_presheaf
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q) :
    (PresheafOfModules.toPresheaf
      (A ⋙ forget₂ CommRingCat RingCat)).map (toPushforward f A g) =
        toUnderlying f A g := rfl

@[simp]
private lemma fromPushforward_presheaf
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ (pushforward f A).obj Q) :
    (PresheafOfModules.toPresheaf
      (LSZ.InverseImagePresheaf.ring f A ⋙
        forget₂ CommRingCat RingCat)).map (fromPushforward f A h) =
      fromUnderlying f A h := rfl

private lemma from_to
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q) :
    fromPushforward f A (toPushforward f A g) = g := by
  apply (PresheafOfModules.toPresheaf
    (LSZ.InverseImagePresheaf.ring f A ⋙
      forget₂ CommRingCat RingCat)).map_injective
  rw [fromPushforward_presheaf]
  change ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M.presheaf Q.presheaf).symm
        ((PresheafOfModules.toPresheaf
          (A ⋙ forget₂ CommRingCat RingCat)).map (toPushforward f A g)) =
    (PresheafOfModules.toPresheaf
      (LSZ.InverseImagePresheaf.ring f A ⋙
        forget₂ CommRingCat RingCat)).map g
  rw [toPushforward_presheaf]
  change ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M.presheaf Q.presheaf).symm
        (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
          M.presheaf Q.presheaf)
            ((PresheafOfModules.toPresheaf
              (LSZ.InverseImagePresheaf.ring f A ⋙
                forget₂ CommRingCat RingCat)).map g)) = _
  exact ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
    M.presheaf Q.presheaf).symm_apply_apply _

private lemma to_from
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ (pushforward f A).obj Q) :
    toPushforward f A (fromPushforward f A h) = h := by
  apply (PresheafOfModules.toPresheaf
    (A ⋙ forget₂ CommRingCat RingCat)).map_injective
  rw [toPushforward_presheaf]
  change (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M.presheaf Q.presheaf
        ((PresheafOfModules.toPresheaf
          (LSZ.InverseImagePresheaf.ring f A ⋙
            forget₂ CommRingCat RingCat)).map (fromPushforward f A h)) =
    (PresheafOfModules.toPresheaf
      (A ⋙ forget₂ CommRingCat RingCat)).map h
  rw [fromPushforward_presheaf]
  change (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M.presheaf Q.presheaf
        (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
          M.presheaf Q.presheaf).symm
            ((PresheafOfModules.toPresheaf
              (A ⋙ forget₂ CommRingCat RingCat)).map h)) = _
  exact ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
    M.presheaf Q.presheaf).apply_symm_apply _

noncomputable def homEquiv
    (M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat))
    (Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)) :
    (LSZ.InverseImagePresheaf.module f A M ⟶ Q) ≃
      (M ⟶ (pushforward f A).obj Q) where
  toFun := toPushforward f A
  invFun := fromPushforward f A
  left_inv := from_to f A
  right_inv := to_from f A

@[simp]
private lemma moduleMap_presheaf
    {M N : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) :
    (PresheafOfModules.toPresheaf
      (LSZ.InverseImagePresheaf.ring f A ⋙
        forget₂ CommRingCat RingCat)).map
        (LSZ.InverseImagePresheaf.moduleMap f A g) =
      (TopCat.Presheaf.pullback Ab.{u} f).map
        ((PresheafOfModules.toPresheaf
          (A ⋙ forget₂ CommRingCat RingCat)).map g) := rfl

@[simp]
private lemma pushforward_map_presheaf
    {Q Q' : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (q : Q ⟶ Q') :
    (PresheafOfModules.toPresheaf
      (A ⋙ forget₂ CommRingCat RingCat)).map
        ((pushforward f A).map q) =
      (TopCat.Presheaf.pushforward Ab.{u} f).map
        ((PresheafOfModules.toPresheaf
          (LSZ.InverseImagePresheaf.ring f A ⋙
            forget₂ CommRingCat RingCat)).map q) := rfl

private lemma homEquiv_naturality_left_symm
    {M' M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : M' ⟶ M) (h : M ⟶ (pushforward f A).obj Q) :
    (homEquiv f A M' Q).symm (g ≫ h) =
      (LSZ.InverseImagePresheaf.moduleFunctor f A).map g ≫
        (homEquiv f A M Q).symm h := by
  change fromPushforward f A (g ≫ h) =
    LSZ.InverseImagePresheaf.moduleMap f A g ≫
      fromPushforward f A h
  apply (PresheafOfModules.toPresheaf
    (LSZ.InverseImagePresheaf.ring f A ⋙
      forget₂ CommRingCat RingCat)).map_injective
  rw [Functor.map_comp, fromPushforward_presheaf,
    moduleMap_presheaf, fromPushforward_presheaf]
  let ug := (PresheafOfModules.toPresheaf
    (A ⋙ forget₂ CommRingCat RingCat)).map g
  let uh : M.presheaf ⟶
      (TopCat.Presheaf.pushforward Ab.{u} f).obj Q.presheaf := by
    exact (PresheafOfModules.toPresheaf
      (A ⋙ forget₂ CommRingCat RingCat)).map h
  change ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M'.presheaf Q.presheaf).symm (ug ≫ uh) =
    (TopCat.Presheaf.pullback Ab.{u} f).map ug ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
        M.presheaf Q.presheaf).symm uh
  exact (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f)
    |>.homEquiv_naturality_left_symm ug uh

private lemma homEquiv_naturality_right
    {M : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}
    {Q Q' : PresheafOfModules.{u}
      (LSZ.InverseImagePresheaf.ring f A ⋙ forget₂ CommRingCat RingCat)}
    (g : LSZ.InverseImagePresheaf.module f A M ⟶ Q) (q : Q ⟶ Q') :
    homEquiv f A M Q' (g ≫ q) =
      homEquiv f A M Q g ≫ (pushforward f A).map q := by
  change toPushforward f A (g ≫ q) =
    toPushforward f A g ≫ (pushforward f A).map q
  apply (PresheafOfModules.toPresheaf
    (A ⋙ forget₂ CommRingCat RingCat)).map_injective
  rw [Functor.map_comp, toPushforward_presheaf,
    toPushforward_presheaf, pushforward_map_presheaf]
  let ug := (PresheafOfModules.toPresheaf
    (LSZ.InverseImagePresheaf.ring f A ⋙
      forget₂ CommRingCat RingCat)).map g
  let uq := (PresheafOfModules.toPresheaf
    (LSZ.InverseImagePresheaf.ring f A ⋙
      forget₂ CommRingCat RingCat)).map q
  change (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
      M.presheaf Q'.presheaf (ug ≫ uq) =
    (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
        M.presheaf Q.presheaf ug ≫
      (TopCat.Presheaf.pushforward Ab.{u} f).map uq
  exact (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f)
    |>.homEquiv_naturality_right ug uq

private noncomputable def coreHomEquiv :
    Adjunction.CoreHomEquiv
      (LSZ.InverseImagePresheaf.moduleFunctor f A) (pushforward f A) where
  homEquiv := homEquiv f A
  homEquiv_naturality_left_symm := homEquiv_naturality_left_symm f A
  homEquiv_naturality_right := homEquiv_naturality_right f A

noncomputable def adjunction :
    LSZ.InverseImagePresheaf.moduleFunctor f A ⊣ pushforward f A :=
  Adjunction.mkOfHomEquiv (coreHomEquiv f A)

end

end LSZ.InverseImageAdjunction
