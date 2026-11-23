import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KillCokPf

def Pointwise : Prop := B1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D) (O : CommRingCat.{0}) (o : D ⟶ O), IE o → BC q i φ (d ≫ o) →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (m : ℤ) (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) (Q : Ideal O), Q.IsPrime →
  ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = Q.comap o.hom ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)

def Assemble : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m),
  (∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = r ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem KillCok_of (hC : Coprod) (hP : Pointwise) (hA : Assemble) : LateralTheory.E.DescLocPf.Fine.KillCok := by
  intro hH q _ i n A Y φ hq P _ het _ D d hD hpts Y' w φ' hpo m _ y
  have hB1 : B1 := hH.2.2.2.2.2.2.1
  have hloc : ∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧
      Q₁.comap e.hom = r ∧ ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro r hr
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts r hr
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hP hB1 q i φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
    exact ⟨D₁, e, Q₁, he, hQ₁, hc.trans hQr, rest⟩
  obtain ⟨E, e, Y'', u, φ'', he, hs, hpo', hy⟩ := hA hC q i φ' m y hloc
  exact ⟨E, e, Y'', u, φ'', he, hs, het d e hD he, hpo', hy⟩

end LateralTheory.E.KillCokPf
