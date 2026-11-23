import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LBoundProof

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mul_le_sq_add_sq (p q : ℝ≥0∞) : p * q ≤ p ^ 2 + q ^ 2 := by
  rcases le_total p q with h | h
  · calc p * q ≤ q * q := by gcongr
      _ = q ^ 2 := (sq q).symm
      _ ≤ _ := le_add_self
  · calc p * q ≤ p * p := by gcongr
      _ = p ^ 2 := (sq p).symm
      _ ≤ _ := le_self_add

theorem lInt_eq {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) :
    lInt D k₁ k₂ τ U = (cutSet E a τ ×ˢ cutSet E b τ).indicator
      (fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  funext x
  by_cases h1 : x.1 ∈ cutSet E a τ <;> by_cases h2 : x.2 ∈ cutSet E b τ <;>
    simp [lInt, chiT, h1, h2, Set.indicator, Set.mem_prod]

theorem enorm_inner_le {ι : Type} (D : Dom E a b) (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) [Fintype ι]
    (u v : Hs (ι := ι) D) (C : ℝ≥0∞) (hu : ‖u‖ₑ ^ 2 ≤ C) (hv : ‖v‖ₑ ^ 2 ≤ C) :
    ‖inner ℂ u (U v)‖ₑ ≤ ‖U‖ₑ * (2 * C) := by
  have h1 : ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact_mod_cast nnnorm_inner_le_nnnorm (𝕜 := ℂ) u (U v)
  calc ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := h1
    _ ≤ ‖u‖ₑ * (‖U‖ₑ * ‖v‖ₑ) := by gcongr; exact U.le_opNorm_enorm v
    _ = ‖U‖ₑ * (‖u‖ₑ * ‖v‖ₑ) := by ring
    _ ≤ ‖U‖ₑ * (‖u‖ₑ ^ 2 + ‖v‖ₑ ^ 2) := by gcongr; exact mul_le_sq_add_sq _ _
    _ ≤ ‖U‖ₑ * (C + C) := by gcongr
    _ = ‖U‖ₑ * (2 * C) := by rw [two_mul]

theorem lBound_of : Mahler → CutCount → LBound := by
  intro hM hC E _ _ _ a b D ι _ k₁ k₂ C₀ Ω hcont hC₀ hΩ hnorm
  obtain ⟨C₁, N, hC₁, hcut⟩ := hC E a b D Ω hΩ
  refine ⟨2 * Fintype.card ι * C₀.toReal * C₁, N, fun τ hτ U => ?_⟩
  set S : Set (H E a b) := cutSet E a τ ×ˢ cutSet E b τ with hS
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  have hSm : MeasurableSet S := ((hM E a τ).1.prod (hM E b τ).1).measurableSet
  have hg : Continuous fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i)) :=
    continuous_finset_sum _ fun i _ => (hcont i).1.inner (U.continuous.comp (hcont i).2)
  have hmeas : AEStronglyMeasurable (lInt D k₁ k₂ τ U) D.ν := by
    rw [lInt_eq]
    exact hg.aestronglyMeasurable.indicator hSm
  set c : ℝ≥0∞ := Fintype.card ι * (‖U‖ₑ * (2 * C₀)) with hc
  have hcr : c = ENNReal.ofReal (Fintype.card ι * (‖U‖ * (2 * C₀.toReal))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₀, ENNReal.ofReal_ofNat]
  have hctop : c ≠ ⊤ := by rw [hcr]; exact ENNReal.ofReal_ne_top
  have hpt : ∀ x, ‖lInt D k₁ k₂ τ U x‖ₑ ≤ c * S.indicator (cnt (ratH E a b) Ω) x := by
    intro x
    rw [lInt_eq]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      calc ‖∑ i, inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ ≤ ∑ i, ‖inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ :=
            enorm_sum_le _ _
        _ ≤ ∑ _i : ι, ‖U‖ₑ * (2 * (C₀ * cnt (ratH E a b) Ω x)) :=
            Finset.sum_le_sum fun i _ => enorm_inner_le D U _ _ _ (hnorm x i).1 (hnorm x i).2
        _ = c * cnt (ratH E a b) Ω x := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
            ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hA : 0 ≤ 2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖ := by positivity
  have hle : ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤
      ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
    calc ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤ ∫⁻ x, c * S.indicator (cnt (ratH E a b) Ω) x ∂D.ν :=
          lintegral_mono hpt
      _ = c * ∫⁻ x, S.indicator (cnt (ratH E a b) Ω) x ∂D.ν := lintegral_const_mul' _ _ hctop
      _ ≤ c * ENNReal.ofReal (C₁ * (1 + τ) ^ N) := by gcongr; exact hcut τ hτ
      _ = ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
          rw [hcr, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine ⟨⟨hmeas, hle.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hA hle

end GlobalTheory.CompanionTheory.LBoundProof

end
