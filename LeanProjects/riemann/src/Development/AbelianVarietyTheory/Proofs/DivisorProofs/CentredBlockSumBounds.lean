import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

theorem centred_block_sum_bounds (N j : ℕ) (u : Fin N → ℝ) (hj : j ≤ N) (hN : 0 < N)
    (hu : ∀ a b : Fin N, a ≤ b → u b ≤ u a) :
    0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N)
      ≤ ∑ i, |u i| ∧ (N : ℝ) * |(∑ i, u i) / N| ≤ ∑ i, |u i| := by
  classical
  set F := Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) with hF
  set G := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j) with hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hcF : F.card = j := by
    rw [hF, Fin.card_filter_val_lt]; omega
  have hcFG : F.card + G.card = N := by
    rw [hF, hG, Finset.card_filter_add_card_filter_not]; simp
  have hcG : (G.card : ℝ) = N - j := by
    have : (F.card : ℝ) + G.card = N := by exact_mod_cast hcFG
    rw [hcF] at this; linarith
  have hS : ∑ i, u i = ∑ i ∈ F, u i + ∑ i ∈ G, u i :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hA : ∑ i, |u i| = ∑ i ∈ F, |u i| + ∑ i ∈ G, |u i| :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hp : 0 ≤ ∑ a ∈ F, ∑ b ∈ G, (u a - u b) := by
    refine Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => sub_nonneg.2 (hu a b ?_)
    simp only [hF, hG, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [Fin.le_def]; omega
  have hp' : 0 ≤ (N - j) * ∑ i ∈ F, u i - j * ∑ i ∈ G, u i := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcF, hcG,
      ← Finset.mul_sum] at hp
    exact hp
  have h1 : |∑ i ∈ F, u i| ≤ ∑ i ∈ F, |u i| := Finset.abs_sum_le_sum_abs _ _
  have h2 : |∑ i ∈ G, u i| ≤ ∑ i ∈ G, |u i| := Finset.abs_sum_le_sum_abs _ _
  have h3 : |∑ i, u i| ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
  have key : ∑ i ∈ F, u i - j * ((∑ i, u i) / N)
      = ((N - j) * ∑ i ∈ F, u i - j * ∑ i ∈ G, u i) / N := by
    rw [hS]; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; exact div_nonneg hp' hNr.le
  · rw [key, div_le_iff₀ hNr, hA]
    have a1 := le_abs_self (∑ i ∈ F, u i)
    have a2 := neg_abs_le (∑ i ∈ G, u i)
    have b1 : 0 ≤ ∑ i ∈ F, |u i| := le_trans (abs_nonneg _) h1
    have b2 : 0 ≤ ∑ i ∈ G, |u i| := le_trans (abs_nonneg _) h2
    have c1 : (N - j) * ∑ i ∈ F, u i ≤ (N - j) * ∑ i ∈ F, |u i| :=
      mul_le_mul_of_nonneg_left (a1.trans h1) (by linarith)
    have c2 : j * (-∑ i ∈ G, u i) ≤ j * ∑ i ∈ G, |u i| :=
      mul_le_mul_of_nonneg_left (by linarith) hj0
    nlinarith [mul_nonneg hj0 b1, mul_nonneg (sub_nonneg.2 hjr) b2]
  · rw [abs_div, abs_of_pos hNr, mul_div_cancel₀ _ hNr.ne']
    exact h3

end GlobalTheory
