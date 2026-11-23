import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormulaStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogIdealEqLogAbsNormStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem different_sum_eq_neg_finrank_mul_log_rootDiscr : ∀ (E : Type) [Field E] [NumberField E], {p : Nat.Primes | ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≠ 0}.Finite ∧ ∑ᶠ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = -(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E) := by
  intro E _ _
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (discr E).natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := hn ▸ Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hsum : ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p],
      GlobalTheory.CompanionTheory.Ar.Fl.logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        Real.log ‖((n : ℚ) : ℂ_[p])‖ := by
    intro p
    rw [GlobalTheory.T.sum_logIdeal_eq_log_absNorm E _ hD p, absNorm_differentIdeal E (𝓞 E), ← hn,
      Rat.cast_natCast]
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.rat_product_formula (n : ℚ) hq
  have h1 : ‖((n : ℚ) : ℂ)‖ = (n : ℝ) := by rw [Rat.cast_natCast, Complex.norm_natCast]
  have hpos : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero E))
  have h2 : Real.log (rootDiscr E) = (Module.finrank ℚ E : ℝ)⁻¹ * Real.log (n : ℝ) := by
    rw [rootDiscr_def, Real.log_rpow hpos, hn, Nat.cast_natAbs]
  have hk : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  simp only [hsum]
  refine ⟨hfin, ?_⟩
  rw [h1] at hprod
  rw [h2, ← mul_assoc, neg_mul, mul_inv_cancel₀ hk.ne', neg_one_mul]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl
