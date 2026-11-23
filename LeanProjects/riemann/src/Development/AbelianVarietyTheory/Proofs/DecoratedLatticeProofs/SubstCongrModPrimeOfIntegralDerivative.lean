import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

open PowerSeries

noncomputable section

namespace GlobalTheory.Honda

theorem subst_congr_of_derivative_integral :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 →
    ∀ (f : K⟦X⟧), CoefLe 1 (derivative K f) → ∀ (s : Type) (A B : MvPowerSeries s K),
    MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 →
    (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) →
    (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) →
    ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0

  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' pow_padicValNat_dvd
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d

end GlobalTheory.Honda
