import Development.EtaleCohomology.EtaleSheaves.RelativeCohomologyForgetInjectiveDegreeZeroOfSub

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHPtPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf

theorem germ (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B : Scheme.{0}} (U : B.Etale) (x : U.left)
    {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (he : ∀ j, IsIso (e j)) (hy : ∀ j, (a j).left (y j) = x)
    (hq : ∀ j, IsUnit ((q : ℕ) : D.obj j))
    (hcomp : ∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left)
    (ht : ∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t)
    (s : Sec (tw q i) U.left) (hs : Sec.res t s = 0) :
    ∃ (U' : B.Etale) (a' : U' ⟶ U) (y' : U'.left), a'.left y' = x ∧ Sec.res a'.left s = 0 := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  have hB1 : B1 := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, eq, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  set z : Ht q (sp (D.obj j)) 0 i := eq _ (Sec.res (e j ≫ (a j).left) s) with hz
  have h0 : pull _ (spMap (c.ι.app j).hom) _ _ z = 0 := by
    rw [hz, spMap, hnat, ← res_comp, ht, hs, map_zero]
  obtain ⟨k, f, hk⟩ := (hB1 q D c hc 0 i).2 j z (hq j) h0
  rw [hz, spMap, hnat, ← res_comp, hcomp] at hk
  have hk' : Sec.res (e k ≫ (a k).left) s = 0 := (eq _).injective (by rw [hk, map_zero])
  refine ⟨V k, a k, y k, hy k, ?_⟩
  have := congrArg (Sec.res (inv (e k))) hk'
  rw [← res_comp, IsIso.inv_hom_id_assoc] at this
  simpa using this

def LeafSHNb : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left), (∀ j, IsIso (e j)) ∧ (∀ j, (a j).left (y j) = x) ∧ (∀ j, IsUnit ((q : ℕ) : D.obj j)) ∧
    (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
    (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧ SH c.pt ∧
    (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left)

def LeafSHTop : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) {J : Type} [SmallCategory J] [Nonempty J]
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
  (t : Sp c.pt ⟶ U.left), (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) →
  (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left) →
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a' : U' ⟶ U), S a' ∧ ∃ t' : Sp c.pt ⟶ U'.left, t' ≫ a'.left = t)

theorem LeafSHPt_of (hN : LeafSHNb) (hT : LeafSHTop) : LeafSHPt := by
  intro hH q _ k _ hq i B U s0 x
  obtain ⟨J, _, _, D, c, hc, V, a, y, e, t, he, hy, hqj, hcomp, ht, hSH, hcof⟩ := hN hH q k hq U s0 x
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨hO, hL⟩ := hT U x D c V a e t ht hcof
  exact ⟨c.pt, inferInstance, t, hSH, hO, hL, fun s hs => germ hH q i U x D c hc V a y e t he hy hqj hcomp ht s hs⟩

end LateralTheory.E.LeafSHPtPf
