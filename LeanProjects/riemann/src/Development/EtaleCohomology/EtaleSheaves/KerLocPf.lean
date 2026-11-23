import Development.EtaleCohomology.EtaleSheaves.LocalDescent

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KerLocPf

def KillKer : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n, pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ P E (d ≫ e) ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

def PtsEt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y D E : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) (e : D ⟶ E),
  IsUnit (q : A) → LocPts q i φ d → Et e → LocPts q i φ (d ≫ e)

def TruncKer : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ'')) (tw q i) m)) →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n,
    pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 → pull _ (sch.map (Spec.map e)) (tw q i) n x = 0 → x = 0

theorem KerLoc_of (hK : KillKer) (hP : PtsEt) (hT : TruncKer) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow hcok D d hD hpts Y' w φ' hpo
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨E, e, Y'', u, φ'', he, hs, hE, hpo', hxE⟩ :=
    hK hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo x hx
  have hptsE : LocPts q i φ (d ≫ e) := hP hH q i φ d e hq hpts he
  have hpoE : IsPushout φ (d ≫ e) (w ≫ u) φ'' := hpo.paste_vert hpo'
  exact hT hH q i n φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
    (hcok D d hD hpts Y' w φ' hpo) (hcok E (d ≫ e) hE hptsE Y'' (w ≫ u) φ'' hpoE) x hx hxE

end LateralTheory.E.KerLocPf
