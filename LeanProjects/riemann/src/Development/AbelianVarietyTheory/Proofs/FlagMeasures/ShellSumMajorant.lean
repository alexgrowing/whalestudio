import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

private lemma exp_mul_exp_neg_eq_shell (a : ℝ) (r : ℕ) :
    Real.exp (2 * a * (r + 1)) * Real.exp (-(4 * a * r)) =
      Real.exp (2 * a) * Real.exp (-(2 * a)) ^ r := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem shell_sum_majorant : ∀ (n q : ℕ) (h : ℝ), 1 ≤ n → 1 ≤ q → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h → AntitoneOn (decE q h) (Set.Ici 0) ∧ (∀ r : ℕ, decE q h r ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ Summable (fun r : ℕ => Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ ∑' r : ℕ, Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r)) ≤ 2 * Real.exp (2 * (n : ℝ) ^ 2) := by
  intro n q h hn hq hh
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr hq1
  have hsqpos : 0 < Real.sqrt (q : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 32 * (n : ℝ) ^ 2 * Real.sqrt q := by positivity
    linarith
  have hgeo := fun r : ℕ => exp_mul_exp_neg_eq_shell ((n : ℝ) ^ 2) r
  have h3 : 3 ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp (2 * (n : ℝ) ^ 2)]
  have he0 : 0 ≤ Real.exp (-(2 * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
  have he : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    have hm : min (2 * x ^ 2) (x / Real.sqrt q) ≤ min (2 * y ^ 2) (y / Real.sqrt q) := by
      apply min_le_min
      · nlinarith
      · exact div_le_div_of_nonneg_right hxy hsqpos.le
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  ·
    intro r
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hmin : min (2 * (r : ℝ) ^ 2) (r / Real.sqrt q) = r / Real.sqrt q := by
        apply min_eq_right
        have : (r : ℝ) / Real.sqrt q ≤ r := div_le_self (by linarith) hsq
        nlinarith
      rw [hmin, neg_mul]
      apply neg_le_neg
      have hd : 32 * (n : ℝ) ^ 2 ≤ h / Real.sqrt q := by
        rw [le_div_iff₀ hsqpos]
        exact hh
      have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ r)
      have hdiv : h / 8 * (r / Real.sqrt q) = h / Real.sqrt q * r / 8 := by ring
      rw [hdiv]
      linarith
  · rw [funext hgeo]
    exact (summable_geometric_of_lt_one he0 (by linarith)).mul_left _
  ·
    rw [funext hgeo, tsum_mul_left, tsum_geometric_of_lt_one he0 (by linarith)]
    have hinv : (1 - Real.exp (-(2 * (n : ℝ) ^ 2)))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (2 * (n : ℝ) ^ 2)).le
    linarith

end GlobalTheory.Dec
