import Development.EtaleCohomology.EtaleSheaves.StalkCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescLocPf

def LocPts (q : ℕ) (i : ℤ) {A Y D : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) : Prop :=
  ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)

def CokLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)

def KerLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → LocPts q i φ c →
    ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  Function.Injective (pull _ (sch.map (Spec.map φ')) (tw q i) n)

theorem DescLoc_of (hC : CokLoc) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo
  exact ⟨hC hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo,
    hK hH q i n φ hq P hpush het hlow (fun C c hC' hpC => hC hH q i n φ hq P hpush het hlow C c hC' hpC) D d hD hpts Y' w φ' hpo⟩

end LateralTheory.E.DescLocPf
