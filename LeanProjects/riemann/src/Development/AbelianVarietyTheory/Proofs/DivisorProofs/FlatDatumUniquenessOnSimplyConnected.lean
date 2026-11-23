import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
open Set Matrix GlobalTheory.TorsionForm GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm.FlatSame

theorem isFactor_transl {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} (hj : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsFactor B τ M j) (x : Fl g) :
    GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsFactor B τ M (translPullFactor τ x j) := by
  refine ⟨fun l hl => ⟨?_, fun P hP => (hj.1 l hl).2 _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)⟩,
    fun l hl l' hl' P hP => ?_⟩
  · exact (hj.1 l hl).1.comp (GlobalTheory.FlatRigidity.differentiableOn_transl hτ x)
      fun P hP => GlobalTheory.FlatRigidity.transl_mem τ x hP
  · have hc : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ x (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l' P) =
        GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l' (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ x P) := by
      rw [GlobalTheory.FlatRigidity.transl_transl, GlobalTheory.FlatRigidity.transl_transl, add_comm]
    simp only [translPullFactor]
    rw [hc]
    exact hj.2 l hl l' hl' _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)

theorem isBundleIso_inv {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j j' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ} (h : IsBundleIso B τ M j j' φ) :
    IsBundleIso B τ M j' j (fun P => (φ P)⁻¹) := by
  refine ⟨h.1.inv h.2.1, fun P hP => inv_ne_zero (h.2.1 P hP), fun l hl P hP => ?_⟩
  have e := h.2.2 l hl P hP
  have h1 := h.2.1 P hP
  have h2 := h.2.1 _ (GlobalTheory.FlatRigidity.transl_mem τ l hP)
  field_simp
  linear_combination -e

theorem isIsometry_inv {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {h h' : Pt E g → ℝ} {φ : Pt E g → ℂ} (hφ : ∀ P ∈ cov B g, φ P ≠ 0)
    (hi : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsIsometry B h h' φ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsIsometry B h' h (fun P => (φ P)⁻¹) := by
  intro P hP
  have h1 : ‖φ P‖ ≠ 0 := norm_ne_zero_iff.2 (hφ P hP)
  rw [← hi P hP, norm_inv]
  field_simp

theorem main : IsometryInv → TranslationInv → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ), SimplyConnectedSpace B → ∀ (M : Submodule ℤ (Fl g)), (∀ l ∈ M, ∀ l' ∈ M, ∃ k : ℤ, riem l l' = k) → ∀ (j₁ j₂ : Fl g → Pt E g → ℂ) (h₁ h₂ : Pt E g → ℝ), IsDatum B τ M j₁ h₁ → ChernIsFlat B τ h₁ → IsDatum B τ M j₂ h₂ → ChernIsFlat B τ h₂ → ∀ (β : Fin n → E), ∀ b ∈ B, ∀ T : Ext (n + n), IsTorsionForm τ M j₁ h₁ β b T → IsTorsionForm τ M j₂ h₂ β b T := by
  intro hI hT E _ _ _ g n B τ hB M hint j₁ j₂ h₁ h₂ hd₁ hc₁ hd₂ hc₂ β b hb T hT₁
  obtain ⟨x, φ, hφ, hiso⟩ := GlobalTheory.FlatRigidity.rigidity hd₁.1 hB M hd₁.2.1 hint j₁ j₂ h₁ h₂
    hd₁.2.2.1 hd₁.2.2.2 hc₁ hd₂.2.2.1 hd₂.2.2.2 hc₂
  have hdx : IsDatum B τ M (translPullFactor τ x j₁)
      (fun P => h₁ (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ x P)) :=
    ⟨hd₁.1, hd₁.2.1, isFactor_transl hd₁.1 hd₁.2.2.1 x,
      (GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat hd₁.1 M j₁ h₁ hd₁.2.2.2 hc₁ x).1⟩
  exact hI E g n B τ M _ j₂ _ h₂ _ hdx hd₂ (isBundleIso_inv hφ) (isIsometry_inv hφ.2.1 hiso) β b hb T
    (hT E g n B τ M j₁ h₁ hd₁ x β b hb T hT₁)

end GlobalTheory.TorsionForm.FlatSame
