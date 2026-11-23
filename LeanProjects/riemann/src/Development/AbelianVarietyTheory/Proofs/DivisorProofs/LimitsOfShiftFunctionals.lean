import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalPowerSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassDegreeOneStatement

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem pSum_isHomogeneous' {ι : Type} {N : ℕ} (τ : ι) (k : ℕ) :
    (pSum τ k : Pol ι N).IsHomogeneous k := by
  unfold pSum
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_X ℝ (τ, i)).pow k

theorem pLow_isHomogeneous' {ι : Type} {N : ℕ} (j : ℕ) (τ : ι) (k : ℕ) :
    (pLow j τ k : Pol ι N).IsHomogeneous k := by
  unfold pLow
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_X ℝ (τ, i)).pow k

theorem coefficients_converge (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) [Nonempty ι] (j : ℕ)
    (a b : ℕ → ℝ) (hj : 1 ≤ j) (hjN : j < N)
    (h : ∀ F : Pol ι N, F.IsHomogeneous (dimFl ι N + 1) → ∃ L : ℝ,
      Filter.Tendsto (fun B => a B * (∑ τ, shF j τ F) + b B * (∑ τ, totF τ F)) Filter.atTop (nhds L)) :
    ∃ A b₀ : ℝ, Filter.Tendsto a Filter.atTop (nhds A) ∧ Filter.Tendsto b Filter.atTop (nhds b₀) := by
  obtain ⟨σ⟩ := ‹Nonempty ι›
  obtain ⟨Q, hQ, hQ1⟩ := GlobalTheory.T.exists_class_degree_one ι N j σ hj hjN
  have hd : 1 ≤ dimFl ι N := by
    have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos
    have h2 : 1 ≤ N * (N - 1) / 2 := by
      have : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    unfold dimFl
    exact Nat.mul_pos h1 h2
  have hF2 : (pSum σ 2 * Q).IsHomogeneous (dimFl ι N + 1) := by
    have := (pSum_isHomogeneous' (N := N) σ 2).mul hQ
    rwa [show 2 + (dimFl ι N - 1) = dimFl ι N + 1 by omega] at this
  have hF1 : (pSum σ 1 * (pLow j σ 1 * Q)).IsHomogeneous (dimFl ι N + 1) := by
    have := (pSum_isHomogeneous' (N := N) σ 1).mul ((pLow_isHomogeneous' (N := N) j σ 1).mul hQ)
    rwa [show 1 + (1 + (dimFl ι N - 1)) = dimFl ι N + 1 by omega] at this
  have s2 : ∑ τ, shF j τ (pSum σ 2 * Q) = 2 := by
    rw [Finset.sum_eq_single σ]
    · rw [(GlobalTheory.T.shift_functional_power_sum ι N j 2 Q σ σ (by norm_num)).1, if_pos rfl]
      norm_num [hQ1]
    · intro τ _ hτ
      rw [(GlobalTheory.T.shift_functional_power_sum ι N j 2 Q τ σ (by norm_num)).1, if_neg hτ]
    · simp
  have t2 : ∑ τ, totF τ (pSum σ 2 * Q) = 0 := by
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [(GlobalTheory.T.shift_functional_power_sum ι N j 2 Q τ σ (by norm_num)).2, if_neg (by simp)]
  have t1 : ∑ τ, totF τ (pSum σ 1 * (pLow j σ 1 * Q)) = N := by
    rw [Finset.sum_eq_single σ]
    · rw [(GlobalTheory.T.shift_functional_power_sum ι N j 1 _ σ σ le_rfl).2, if_pos ⟨rfl, rfl⟩, hQ1, mul_one]
    · intro τ _ hτ
      rw [(GlobalTheory.T.shift_functional_power_sum ι N j 1 _ τ σ le_rfl).2, if_neg (fun h => hτ h.1)]
    · simp
  obtain ⟨L2, hL2⟩ := h _ hF2
  obtain ⟨L1, hL1⟩ := h _ hF1
  rw [s2, t2] at hL2
  rw [t1] at hL1
  set s := ∑ τ, shF j τ (pSum σ 1 * (pLow j σ 1 * Q))
  have ha : Filter.Tendsto a Filter.atTop (nhds (L2 / 2)) :=
    (hL2.div_const 2).congr fun B => by ring
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  refine ⟨_, (L1 - L2 / 2 * s) / N, ha, ?_⟩
  refine ((hL1.sub (ha.mul_const s)).div_const (N : ℝ)).congr fun B => ?_
  field_simp
  ring

end GlobalTheory.FlagPoly
