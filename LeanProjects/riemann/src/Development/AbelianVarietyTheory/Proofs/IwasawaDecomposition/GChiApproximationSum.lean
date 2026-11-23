import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TailAndSumBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiPowerSavingBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBoundStatement

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.GoodCharacterSum

theorem gChi_add_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x z : ℝ)
    (hx : 0 ≤ x) (hz : x ≤ z) :
    GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊z⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      -((x : ℂ) * (-GlobalTheoryTheory.logDerivativeAtOne χ -
        ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ))) := by
  have h1 : GlobalTheoryTheory.sumLamChi χ x = ∑ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) := by
    unfold GlobalTheoryTheory.sumLamChi
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hz))
    intro n hn hn'
    have h1n : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hlt : ⌊x⌋₊ < n := by
      by_contra h
      exact hn' (Finset.mem_Icc.2 ⟨h1n, not_lt.1 h⟩)
    have hxn : x < n := (Nat.floor_lt hx).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1n
    have : x / n - 1 ≤ 0 := by
      have := (div_le_one hn0).2 hxn.le
      linarith
    rw [max_eq_right this]
    simp
  have h2 : ∀ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) +
        (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) := by
    intro n _
    have hm : max (x / n - 1) 0 + min 1 (x / n) = x / n := by
      rcases le_total 1 (x / n) with h | h
      · rw [max_eq_left (by linarith), min_eq_left h]; ring
      · rw [max_eq_right (by linarith), min_eq_right h]; ring
    have hm' : ((max (x / n - 1) 0 : ℝ) : ℂ) + ((min 1 (x / n) : ℝ) : ℂ) = (x : ℂ) / (n : ℂ) := by
      rw [← Complex.ofReal_add, hm]; push_cast; rfl
    unfold GlobalTheoryTheory.cn
    rw [Complex.ofReal_mul]
    linear_combination (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) * hm'
  unfold GlobalTheoryTheory.gChi
  rw [if_neg hχ, h1, mul_sub, Finset.mul_sum, ← Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

theorem gChi_add_sum_bound : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q)‖ ≤ x ^ eps ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x := by
  intro hZ hC hL hN hF eps h0 h1
  obtain ⟨C₁, hC₁, H1⟩ := GlobalTheory.T.psi_chi_power_saving_bound hC hL hN hF hZ
  obtain ⟨C₂, c₂, hC₂, hc₂, H2⟩ := GlobalTheory.T.psi_chi_sqrt_log_bound hC hL hN hF hZ
  obtain ⟨CM, hCM, HM⟩ : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := GlobalTheory.mertens_first_vonMangoldt
  have HS := GlobalTheory.T.log_deriv_series_of_explicit hZ hC hL hN hF
  obtain ⟨x₀, C, HT⟩ := GlobalTheory.GoodCharacterTail.tail_and_sum_bound eps h0 (by linarith)
    (max C₁ C₂) c₂ CM (lt_max_of_lt_left hC₁) hc₂ hCM
  refine ⟨max x₀ (max 1 ((2 : ℝ) ^ (6 / eps))), max C 1, lt_max_of_lt_right one_pos, ?_⟩
  intro x hx Q q _ χ hQ hl hu hχ hg
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ^ (6 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have h2 : (2 : ℝ) ≤ x ^ (eps / 6) := by
    have := Real.rpow_le_rpow (by positivity) hx2 (by positivity : 0 ≤ eps / 6)
    rw [← Real.rpow_mul (by norm_num), show 6 / eps * (eps / 6) = 1 by field_simp, Real.rpow_one] at this
    exact this
  have hQ3 : 3 ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ
    linarith
  have key := HT x hx0 Q hQ hl hu (fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (-GlobalTheoryTheory.logDerivativeAtOne χ)
    (HS q χ hχ) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have hz : x ≤ x ^ (400 : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 400)
        rwa [Real.rpow_one] at this
      rw [gChi_add_sum_eq χ hχ x _ (by linarith) hz, norm_neg]
      exact key.1
    · have := key.2
      rw [norm_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hx1))
  · intro y hy
    have := (abs_le.1 (HM y hy)).2
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (by linarith : ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)
  · intro u hu2
    refine le_trans (H1 Q q χ hQ3 hχ hg u hu2) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 < u := by linarith
    positivity
  · intro u hu2
    have : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu2
    refine le_trans (H2 Q q χ hQ3 hχ hg u hu2) ?_
    gcongr
    exact le_max_right _ _

end GlobalTheory.GoodCharacterSum
