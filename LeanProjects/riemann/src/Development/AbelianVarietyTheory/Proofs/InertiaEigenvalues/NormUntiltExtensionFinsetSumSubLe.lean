import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_ext_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F)
    (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  intro l _ F _ ι tsh hn hι hsurj α s z R hR hz
  classical
  obtain ⟨-, -, -, -, -, hon, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := GlobalTheory.PSer.Laws.norm_l
  have hlpos : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hlpos
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; exact inv_pos.2 (by linarith)
  obtain ⟨w, hw⟩ := hon (l : ℂ_[l]) hl1.le
  have hnw : ‖ι w‖ = ‖(l : ℂ_[l])‖ := by rw [← hn, hι, hw]

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖ι w‖ ^ N * R ≤ 1 := by
    rcases le_or_gt R 1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0:ℝ) < R)) (hnw ▸ hl1)
      refine ⟨N, ?_⟩
      have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℝ) < R)
      rw [inv_mul_cancel₀ (by linarith)] at this
      exact this.le
  set c : F := ι w ^ N with hc
  have hcn : ‖c‖ = ‖ι w‖ ^ N := by rw [hc, norm_pow]
  have hcpos : 0 < ‖c‖ := by rw [hcn, hnw]; exact pow_pos hl0 N
  have hx : ∀ a, ∃ x : Fl l, ι x = if a ∈ s then c * z a else 0 := by
    intro a
    split_ifs with ha
    · refine hsurj _ ?_
      rw [norm_mul, hcn]
      calc ‖ι w‖ ^ N * ‖z a‖ ≤ ‖ι w‖ ^ N * R :=
            mul_le_mul_of_nonneg_left (hz a ha) (pow_nonneg (norm_nonneg _) _)
        _ ≤ 1 := hN
    · exact ⟨0, map_zero ι⟩
  choose x hxe using hx
  have hxa : ∀ a ∈ s, ι (x a) = c * z a := fun a ha => by rw [hxe, if_pos ha]
  have hsa : ∀ a ∈ s, sh (x a) = tsh c * tsh (z a) := fun a ha => by
    rw [← hι, hxa a ha, map_mul]
  have hss : sh (∑ a ∈ s, x a) = tsh c * tsh (∑ a ∈ s, z a) := by
    rw [← hι, map_sum, Finset.sum_congr rfl hxa, ← Finset.mul_sum, map_mul]
  have hbd : ∀ a ∈ s, ‖sh (x a)‖ ≤ ‖c‖ * R := fun a ha => by
    rw [hsa a ha, norm_mul, hn, hn]
    exact mul_le_mul_of_nonneg_left (hz a ha) (norm_nonneg _)
  have key := (untilt_sum_sub_le l α s (‖c‖ * R) x (mul_nonneg (norm_nonneg _) hR) hbd).1
  rw [hss, Finset.sum_congr rfl hsa, ← Finset.mul_sum, ← mul_sub, norm_mul, hn] at key
  have : ‖c‖ * ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖c‖ * (‖(l : ℂ_[l])‖ * R) := by
    linarith [key]
  exact le_of_mul_le_mul_left this hcpos

end GlobalTheory
