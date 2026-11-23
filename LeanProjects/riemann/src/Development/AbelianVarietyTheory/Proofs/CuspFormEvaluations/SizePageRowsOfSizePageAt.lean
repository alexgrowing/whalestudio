import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_pageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hPg hCK
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  obtain ⟨Q, PT, -, hC, hA⟩ := hPg
  have hPP : WeightFamilies.PPv D large₂ C2 A2 = PT.PP := by rw [← hC, ← hA]; exact WeightFamilies.PPv_rec PT
  obtain ⟨hA', hS, -, h4, -⟩ := hp
  obtain ⟨-, -, -, -, hg, -, -, hp1, hp2, -⟩ := hA'
  obtain ⟨hn, -, -, -, -, -, -, hsz, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS
  obtain ⟨-, -, -, hP3, -⟩ := h4
  rw [hPP] at hCK hP3
  have hL := EtaleWeightGaps.Num.Pm.one_le_L large₂
  have hf2 := EtaleWeightGaps.Num.Pm.two_le_f D
  have hr6 := EtaleWeightGaps.Num.Pm.six_le_r D
  have hm2 := EtaleWeightGaps.Num.Pm.two_le_m D
  have hkr := EtaleWeightGaps.Num.Pm.k_le_r D
  have hrt := EtaleWeightGaps.Num.Pm.r_le_alt_alt D
  have hlf := EtaleWeightGaps.Num.Pm.log_f_le Q
  have hlr := EtaleWeightGaps.Num.Pm.log_r_le Q
  obtain ⟨hlc, hlt⟩ := EtaleWeightGaps.Num.Pm.log_cond_le Q
  have hb : Real.log large₂.sc.b = large₂.sc.L := EtaleWeightGaps.Num.Pm.log_b large₂
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hf0 : (0 : ℝ) < D.R.f := by linarith
  have hr0 : (0 : ℝ) < D.R.r := by linarith
  have hP0 : 0 < PT.PP := PT.PP_pos (by unfold zBase; positivity)
  refine ⟨⟨hg, ?_, ?_, ?_, ?_, hp1, hp2, ?_, ?_⟩, ?_⟩
  · rw [EtaleWeightGaps.Num.Pm.lrd_eq]; linarith [log_rdE_le_scL Q]
  · have hd := EtaleWeightGaps.Num.Pm.one_le_d D
    have hq := EtaleWeightGaps.Num.Pm.one_le_q D
    have h1 : (D.host.d : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
      rw [EtaleWeightGaps.Num.Pm.condE_cast]
      have hS : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
      have : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
      nlinarith
    linarith [Real.log_le_log (by linarith) h1]
  · linarith [Q.ccK_log]
  · linarith
  · have hs : 1 + (WeightAlgebra.DF ka : ℝ) ≤ ka.size := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
      have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by positivity
      push_cast at h2 ⊢
      linarith
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hT1 : (1 : ℝ) ≤ (Tn : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hT)
    have hP3' : PT.PP ^ 3 ≤ large₂.sc.b := (le_mul_of_one_le_right (by positivity) hT1).trans hP3
    have hlP : 3 * Real.log PT.PP ≤ large₂.sc.L := by
      have := Real.log_le_log (by positivity) hP3'
      rw [Real.log_pow, hb] at this
      exact_mod_cast this
    have h1 : H.CK ≤ PT.PP ^ 2 * D.R.f := by
      have : 0 ≤ PT.PP ^ 2 * D.R.f := by positivity
      linarith
    have h2 : H.CK * D.R.k ≤ PT.PP ^ 2 * D.R.f * D.R.r := mul_le_mul h1 hkr hk0 (by positivity)
    have h3 : H.CK * D.R.k * D.R.f * large₂.sc.b ≤ PT.PP ^ 2 * D.R.f * D.R.r * D.R.f * large₂.sc.b := by gcongr
    have h4 := Real.log_le_log (by positivity) (hs.trans (hsz.trans h3))
    rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hf0.ne',
      Real.log_mul (by positivity) hr0.ne', Real.log_mul (by positivity) hf0.ne', Real.log_pow, hb] at h4
    push_cast at h4
    linarith
  · have h1 : (ka.n : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by
      rw [hn]; unfold Ranks.nV; push_cast; nlinarith
    have h2 : (0 : ℝ) < ka.n := by rw [hn]; unfold Ranks.nV; push_cast; linarith
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  · have : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm2 4
    have h : (16 : ℝ) ≤ D.R.f := by linarith
    exact_mod_cast h

end GlobalTheory
