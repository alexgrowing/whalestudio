import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalfStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRootDiscriminantClausesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisonsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsGapsExceedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem standingHypotheses_of_glob0_nodes_Tr_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD →
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' →
      Glob0 D x eps CD Cg → Nodes D x eps →
      (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) →
      StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  intro eps CD he he52 hCD C' Cl Cg hCl hClD
  obtain ⟨x1, h1⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD C'
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD Cl
  obtain ⟨x3, h3⟩ := GlobalTheory.T.globalRankNumberBounds_rootDiscriminant_clauses eps CD he he52 hCD Cl hCl
  obtain ⟨x4, h4⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he52 hCD Cl hCl
  obtain ⟨x5, h5⟩ := GlobalTheory.T.globalRankNumberBounds_gaps_exceed eps CD he he52 hCD Cl hCl
  refine ⟨max x1 (max x2 (max x3 (max x4 x5))), fun x hx D large₂ cT CT hL h8 G N hT => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hx4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have R := G.nums
  obtain ⟨a1, -, -, -, -, -, -, -⟩ := h1 x hx1 _ _ _ _ _ R
  obtain ⟨-, a2, a3, a4, a5, -, -, -⟩ := h2 x hx2 _ _ _ _ _ R
  obtain ⟨c1, c2, c3⟩ := h3 x hx3 _ _ _ _ _ R
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := h4 x hx4 _ _ _ _ _ R
  have e := h5 x hx5 _ _ _ _ _ R (D.R.r : ℝ) k_le_r r_le_two_k
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hb : large₂.sc.b = bx x eps := by
    show Real.exp large₂.sc.L = Real.exp (x ^ eps)
    rw [hL]
  have hrd := G.rd_lo
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hbj : ∀ τ j, 1 ≤ j → j ≤ D.R.m → Real.sqrt (bx x eps) ≤ bOne D τ j ∧ bOne D τ j ≤ bx x eps ^ 2 := by
    intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ j (by omega)]
    exact N.b_win τ ⟨j, by omega⟩
  have hrS : (D.R.rS : ℝ) = (D.R.m : ℝ) / 2 - 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have h' : D.R.rS + 1 = a := by unfold Ranks.rS; omega
    have e1 : (D.R.rS : ℝ) + 1 = a := by exact_mod_cast h'
    have e2 : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    linarith
  rw [hb] at hT
  unfold StandingHypotheses
  dsimp only
  rw [hb, hL]
  refine ⟨h8, a1, by exact_mod_cast R.mf, by exact_mod_cast R.fk, by rw [hrS]; exact a2, a3, a4, ?_, ?_, c2, c3,
    (G.g_win 0).1, (G.g_win 0).2, (G.g_win 1).1, (G.g_win 1).2, ?_, ?_, ?_, ?_, d7 hClD, ?_, ?_, hT, a5, hCl⟩
  · intro τ j h1 h2
    exact le_trans d2 (hbj τ j h1 h2).1
  · rw [hv, Real.log_div (by linarith) (by norm_num)]
    exact c1
  · intro τ j h1 h2
    rw [Real.rpow_two]
    exact ⟨le_trans d3 (hbj τ j h1 h2).1, (hbj τ j h1 h2).2⟩
  · intro τ
    have a := N.bm τ
    have e' : D.R.m = D.R.m - 1 + 1 := by omega
    have b := bOne_succ τ (D.R.m - 1) (by omega)
    rw [← e'] at b
    have b0 : bOne D τ 1 = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := bOne_succ τ 0 (by omega)
    rw [b, b0]
    exact a
  · intro u τ
    have e1 : uOne D u τ 1 = uFirst D τ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 k_pos, D.hcW_first u τ k_pos]
      rfl
    rw [e1]
    by_cases ht : Top D τ
    · exact le_trans (N.top τ ht).2.1 d6
    · have o := (G.off τ ht).2.1
      have v0 := (G.cloud τ ⟨0, by omega⟩).2
      have v0' : vFirst D τ ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) := v0
      linarith
  · rw [hv]; linarith
  · intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ (j + 1) (by omega), bOne_succ τ j (by omega)]
    have g := G.gap τ j (by omega)
    push_cast at g
    linarith [e.2.2.2]
  · intro τ i h
    by_cases c1 : i.1 + 1 < D.R.k - 1
    · rw [lamS_lo τ i (by omega), lamS_lo τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 (by omega),
        vOne_succ τ (i.1 + 1) c1]
      have g := D.s.cloud_gap D.u₀ τ i.1 c1
      simp only [D.hcW_v] at g
      have g' := congrArg (fun q : ℚ => (q : ℝ)) g
      push_cast at g'
      linarith [e.1]
    · by_cases c2 : i.1 < D.R.k - 1
      · rw [lamS_lo τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 c2]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = 0 + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ 0 (by omega)]
        have v0 := (G.cloud τ ⟨i.1, c2⟩).1
        have b0 := (N.b_win τ ⟨0, by omega⟩).1
        linarith [e.2.1]
      · have hi := i.isLt
        rw [lamS_hi τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = (i.1 - (D.R.k - 1) + 1) + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ (i.1 - (D.R.k - 1)) (by omega), bOne_succ τ (i.1 - (D.R.k - 1) + 1) (by omega)]
        have g := G.gap τ (i.1 - (D.R.k - 1)) (by omega)
        push_cast at g
        linarith [e.2.2.1]

end GlobalTheory.Diag.PG
