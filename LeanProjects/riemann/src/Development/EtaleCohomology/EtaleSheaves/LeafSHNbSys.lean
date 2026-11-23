import Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianNeighbourhood

def IsPtNb {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) : Prop :=
  s default = x ∧ (∀ j, IsIso (e j)) ∧ (∀ j, l j ≫ e j ≫ (a j).left = s) ∧
  (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
  (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧
  (∀ (j k : J) (f : j ⟶ k), l k ≫ Spec.map (CommRingCat.ofHom (D.map f).hom) = l j) ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (l' : Spec (CommRingCat.of Ω) ⟶ U'.left), l' ≫ b.left = s →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left ∧ l j ≫ e j ≫ g = l') ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (j : J) (g g' : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left →
      g' ≫ b.left = (a j).left → l j ≫ e j ≫ g = l j ≫ e j ≫ g' →
      ∃ (k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g =
        Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g')

def LeafSHNbSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left),
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t

def LeafSHLoc : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt

def LeafSHHens : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt →
  SH c.pt

theorem LeafSHNb_of (hS : LeafSHNbSys) (hL : LeafSHLoc) (hH : LeafSHHens) : LeafSHNb := by
  intro _ q _ k _ hq B U s0 x
  obtain ⟨Ω, _, _, s, J, _, _, D, c, hc, V, a, l, e, t, hP⟩ := hS U x
  obtain ⟨hs, he, hl, hcomp, ht, -, hcof, -⟩ := id hP
  refine ⟨J, inferInstance, inferInstance, D, c, hc, V, a, fun j => (l j ≫ e j) default, e, t, he, ?_, ?_, hcomp, ht,
    hH U x Ω s D c hc V a l e t hP (hL U x Ω s D c hc V a l e t hP), ?_⟩
  · intro j
    rw [← hs, ← hl j]
    rfl
  · intro j
    have := hq.map (Spec.preimage (e j ≫ (a j).left ≫ s0)).hom
    simpa using this
  · intro U' b y' hy'
    obtain ⟨l', hl', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed b.left s y' (hy'.trans hs.symm)
    obtain ⟨j, g, hg, -⟩ := hcof U' b l' hl'
    exact ⟨j, g, hg⟩

end LateralTheory.E.StrictHenselianNeighbourhood
