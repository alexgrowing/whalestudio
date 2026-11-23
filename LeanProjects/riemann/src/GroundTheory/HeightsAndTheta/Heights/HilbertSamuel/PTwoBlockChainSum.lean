import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IdxAssembleStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm Filter Asymptotics

noncomputable section

theorem TwoBlockChainSum.gridSum_chain (D i : ℕ) (hi : i ≤ D) :
    (fun n : ℕ => (∑ j ∈ Finset.range n,
        ((n - j - 1 : ℕ) : ℝ) ^ i * (j : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  refine (GridSum.proof D i hi).congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  have e1 : n - 1 - (n - j - 1) = j := by omega
  have e2 : n - 1 - j = n - j - 1 := by omega
  simp only [e1, e2]

theorem TwoBlockChainSum.gPoly_chain (D : ℕ) (c : ℕ → ℝ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n, gPoly D c (n - j - 1) j -
      (∑ i ∈ Finset.range (D + 1), c i) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
  refine (IsBigO.fun_sum fun i hi => (TwoBlockChainSum.gridSum_chain D i
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).const_mul_left (c i)).congr_left fun n => ?_
  unfold gPoly
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Finset.mul_sum]
  ring

theorem TwoBlockChainSum.proof (hL : TwoBlockStepLocal.Statement) (hB : TwoBlockStepBound.Statement) :
    TwoBlockChainSum.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨a₀, C, hC⟩ := hL D Ω κ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨K, hK⟩ := hB D Ω κ x B hX hx hBi hsp
  rw [← sum_twoBlockCoeff]
  generalize twoBlockCoeff I x (matAct B x) m m' D = c at hC ⊢
  generalize twoBlockStep x (matAct B x) = s at hC hK ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ i ∈ Finset.range (D + 1), |c i| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ Finset.sum_nonneg fun i _ => abs_nonneg _

  have hterm : ∀ n j : ℕ, j < n →
      |s (n - j - 1) j - gPoly D c (n - j - 1) j| ≤
        if a₀ ≤ n - j - 1 ∧ a₀ ≤ j then |C| * ((n : ℝ) ^ D / n) else (|K| + G) * (n : ℝ) ^ D := by
    intro n j hj
    have hn : ((n - j - 1 : ℕ) : ℝ) + (j : ℝ) + 1 = n := by
      have : n - j - 1 + j + 1 = n := by omega
      exact_mod_cast this
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    split_ifs with h
    · have h1 := hC (n - j - 1) j h.1 h.2
      rw [hn] at h1
      refine le_trans h1 ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    · have hg := abs_gPoly_le D c (n - j - 1) j
      have hn' : ((n - j - 1 + j : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_add]; exact hn
      rw [hn', ← hG] at hg
      have hk := hK (n - j - 1) j
      rw [hn] at hk
      have hk' : K * (n : ℝ) ^ D ≤ |K| * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self K) hpow
      calc _ ≤ |s (n - j - 1) j| + |gPoly D c (n - j - 1) j| := abs_sub _ _
        _ ≤ _ := by linarith

  have h1 : (fun n : ℕ => ∑ j ∈ Finset.range n, (s (n - j - 1) j - gPoly D c (n - j - 1) j)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.of_bound (|C| + 2 * a₀ * (|K| + G)) (Eventually.of_forall fun n => ?_)
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm n j (Finset.mem_range.mp hj)).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hgood : ((Finset.filter (fun j => a₀ ≤ n - j - 1 ∧ a₀ ≤ j) (Finset.range n)).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have hbad : ((Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card : ℝ) ≤ 2 * a₀ := by
      have hsub : Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n) ⊆
          Finset.range a₀ ∪ Finset.Ico (n - a₀) n := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_range, Nat.card_Ico] at hc
      have hc' : (Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card ≤ 2 * a₀ := by
        omega
      exact_mod_cast hc'
    have hcn : (n : ℝ) * ((n : ℝ) ^ D / n) ≤ (n : ℝ) ^ D := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.cast_zero, zero_mul]
        positivity
      · rw [mul_div_cancel₀]
        exact_mod_cast hn.ne'
    have hq : 0 ≤ (n : ℝ) ^ D / n := by positivity
    have hKG : 0 ≤ (|K| + G) * (n : ℝ) ^ D := mul_nonneg (add_nonneg (abs_nonneg K) hG0) hpow
    have e1 := mul_le_mul_of_nonneg_right hgood (mul_nonneg (abs_nonneg C) hq)
    have e2 := mul_le_mul_of_nonneg_right hbad hKG
    have e3 := mul_le_mul_of_nonneg_left hcn (abs_nonneg C)
    nlinarith
  refine (h1.add (TwoBlockChainSum.gPoly_chain D c)).congr_left fun n => ?_
  simp only [Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
