import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

open IsDedekindDomain NumberField

namespace GlobalTheory.AbsNormAdicBounds

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_norm_eq_zpow (y : v.adicCompletion F) (hy : y ≠ 0) :
    ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  simp

theorem norm_absNorm_lt_one :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have h := (NumberField.FinitePlace.norm_lt_one_iff_mem F v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem v.asIdeal)
  rwa [map_natCast, map_natCast] at h

theorem norm_absNorm_mul_le_one :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ * (Ideal.absNorm v.asIdeal : ℝ) ≤ 1 := by
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases h0 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = 0
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ := exists_norm_eq_zpow v _ h0
    have hlt := norm_absNorm_lt_one v
    rw [hk] at hlt ⊢
    have hk0 : k < 0 := (zpow_lt_one_iff_right₀ hq).1 hlt
    rw [← zpow_add_one₀ (by linarith)]
    exact zpow_le_one_of_nonpos₀ hq.le (by omega)

theorem exists_nat_mul_norm_le_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (H : ℝ) (hH : 1 ≤ H) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ H ∧
      ∀ y : v.adicCompletion F, ‖y‖ ≤ H → ‖(n : v.adicCompletion F) * y‖ ≤ 1 := by
  have hqN := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hqN
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hH hq
  refine ⟨Ideal.absNorm v.asIdeal ^ m, pow_pos (by omega) m, by exact_mod_cast hm1, ?_⟩
  intro y hy
  have hyle : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
    by_cases h0 : y = 0
    · rw [h0, norm_zero]; positivity
    · obtain ⟨k, hk⟩ := exists_norm_eq_zpow v y h0
      have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ k <
          (Ideal.absNorm v.asIdeal : ℝ) ^ ((m + 1 : ℕ) : ℤ) := by
        rw [zpow_natCast, ← hk]; exact hy.trans_lt hm2
      have hkm : k < ((m + 1 : ℕ) : ℤ) := (zpow_lt_zpow_iff_right₀ hq).1 hlt
      rw [hk, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hq.le (by push_cast at hkm; omega)
  rw [norm_mul, Nat.cast_pow, norm_pow]
  calc ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ m * ‖y‖
      ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ m *
          (Ideal.absNorm v.asIdeal : ℝ) ^ m := by gcongr
    _ = (‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ *
          (Ideal.absNorm v.asIdeal : ℝ)) ^ m := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ (by positivity) (norm_absNorm_mul_le_one v)

end GlobalTheory.AbsNormAdicBounds
