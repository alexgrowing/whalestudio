import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KillsTranslatesSumMulMeanDifferenceEqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem norm_trm_le (j : ℕ) (s : ℝ) (hj : j ≠ 0) (z : ℂ) : ‖trm j s z‖ ≤ ‖z‖ ^ (-((j : ℝ) + 2 * s)) := by
  by_cases hz : z = 0
  · subst hz
    simp only [trm, zero_pow hj, inv_zero, zero_mul, norm_zero]
    exact Real.rpow_nonneg le_rfl _
  · have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    unfold trm
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _),
      show -((j : ℝ) + 2 * s) = -(j : ℝ) + -2 * s by ring, Real.rpow_add h0, Real.rpow_neg h0.le,
      Real.rpow_natCast]

theorem lat_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  intro j L s v Φ τ hj hs hL hΦ hK
  have hk : (2 : ℝ) < j + 2 * s := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hG : Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖ := by
    have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
      ((EisensteinSeries.r τ) ^ (-((j : ℝ) + 2 * s)))
    have h2 : Summable (fun x : Fin 2 → ℤ => ‖trm j s ((x 0 : ℂ) * τ + x 1)‖) :=
      Summable.of_nonneg_of_le (fun x => norm_nonneg _)
        (fun x => (norm_trm_le j s (by omega) _).trans (EisensteinSeries.summand_bound τ (by linarith) x)) h1
    have h3 := ((finTwoArrowEquiv ℤ).symm.summable_iff).mpr h2
    exact h3.congr fun p => by simp
  obtain ⟨h1s, h1e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK hG
  obtain ⟨_, h2e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK h1s
  refine ⟨hG, ?_⟩
  unfold lat
  rw [h2e, h1e]

end GlobalTheory.EisM
