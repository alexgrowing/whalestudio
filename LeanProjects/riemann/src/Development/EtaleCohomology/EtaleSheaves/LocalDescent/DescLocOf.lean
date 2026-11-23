import Development.EtaleCohomology.EtaleSheaves.LocalDescent

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.DescLocPf.Fine

def KillCok : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → ∀ y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m,
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ P E (d ≫ e) ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

def TruncCok : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∀ m : ℤ, m + 1 = n → ∀ y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m,
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m) →
    y ∈ Set.range (pull _ (sch.map (Spec.map φ')) (tw q i) m)

theorem CokLoc_of (hK : KillCok) (hT : TruncCok) : CokLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo m hm y
  obtain ⟨E, e, Y'', u, φ'', he, hs, hE, hpo', hy⟩ := hK hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo m hm y
  exact hT hH q i n φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y hy

theorem DescLoc_of' (hKC : KillCok) (hTC : TruncCok) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc :=
  DescLoc_of (CokLoc_of hKC hTC) hK

end LateralTheory.E.DescLocPf.Fine
