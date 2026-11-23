import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PPAS

theorem hasTheta_pull_cancel : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (P' : PPAS T) (f : T ⟶ S)
    (φ : P'.A.left ⟶ P.A.left) (g : T' ⟶ T), P'.IsPull P f φ →
    (∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta) →
    ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P'.A.left), Q.IsPull P' g ψ ∧ Q.HasTheta := by
  intro S T T' P P' f φ g hP ⟨Q, ψ, ⟨hQ, hQc⟩, hθ⟩
  obtain ⟨hP, hPc⟩ := hP
  have w : ψ ≫ P.A.hom = (Q.A.hom ≫ g) ≫ f := by
    rw [hQ.1.w, Category.assoc]
  let ψ' : Q.A.left ⟶ P'.A.left := hP.1.lift ψ (Q.A.hom ≫ g) w
  have h₁ : ψ' ≫ φ = ψ := hP.1.lift_fst _ _ _
  have h₂ : ψ' ≫ P'.A.hom = Q.A.hom ≫ g := hP.1.lift_snd _ _ _
  have n : IsGrpPullback Q.A P.A (g ≫ f) (ψ' ≫ φ) := hQ.congr rfl h₁.symm
  have hc : IsGrpPullback Q.A P'.A g ψ' := IsGrpPullback.cancel hP n h₂
  refine ⟨Q, ψ', ⟨hc, ?_⟩, hθ⟩
  have e : sqMap hc.1.w ≫ sqMap hP.1.w = sqMap hQ.1.w := by
    apply Limits.pullback.hom_ext
    · simp only [sqMap, Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst,
        Limits.pullback.lift_fst_assoc]
      rw [h₁]
    · simp only [sqMap, Limits.pullback.map, Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd_assoc]
      rw [h₁]
  rw [hQc, hPc, ← CechPic.pull_comp, e]

end GlobalTheory.PPAS
