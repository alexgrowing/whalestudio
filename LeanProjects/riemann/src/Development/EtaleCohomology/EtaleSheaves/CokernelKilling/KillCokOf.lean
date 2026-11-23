import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.AssembleOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KillCokPf.Glue

theorem et_pi {D : CommRingCat.{0}} {ι : Type} [Finite ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k)
    (he : ∀ k, Et (e k)) : Et (piMap D₁ e) := by
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  haveI : ∀ k, Algebra.Etale D (D₁ k) := he
  have h : Algebra.Etale D (∀ k, D₁ k) := inferInstance
  exact h

def PushGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k),
  (∀ k, Et (e k)) →
  (∀ k, ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ k ⟶ Y₁), IsPushout φ' (e k) u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ Y''),
    IsPushout φ' (piMap D₁ e) u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem ProdGlue_of (hP : PushGlue) : ProdGlue := by
  intro hC q _ i D Y' φ' m y ι _ D₁ e he hk
  exact ⟨et_pi D₁ e he, hP hC q i φ' m y D₁ e he hk⟩

theorem KillCok_of' (hC : Coprod) (hP : LateralTheory.E.KillCokPf.Pointwise) (hG : PushGlue) : LateralTheory.E.DescLocPf.Fine.KillCok :=
  LateralTheory.E.KillCokPf.KillCok_of hC hP (Assemble_of (ProdGlue_of hG))

end LateralTheory.E.KillCokPf.Glue
