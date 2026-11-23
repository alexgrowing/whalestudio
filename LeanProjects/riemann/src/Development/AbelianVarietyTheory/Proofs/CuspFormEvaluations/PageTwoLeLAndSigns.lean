import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem page_two_le_L_and_signs : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 2 ≤ large₂.sc.L ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r ∧ 0 ≤ lamStar D ∧ (1 ≤ j → 1 ≤ WeightFamilies.dimY D j) ∧ (FamilyHypotheses.SupBoundPageRows D large₂ ka ↔ ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hc
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by unfold Ranks.r; omega
  refine ⟨?_, hf, hr, ?_, ?_, Iff.rfl⟩
  · obtain ⟨-, hS, -⟩ := hp
    have hn : ka.n = D.R.nV := hS.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hZ, -⟩ := hS
    obtain ⟨-, -, -, -, hlf, -, -, -, hln⟩ := hc
    by_contra hL
    push_neg at hL
    have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
    have hr0 : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
    have hrn : (D.R.r : ℝ) ≤ ka.n := by
      rw [hn]; exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have he4 : Real.exp 4 ≤ 81 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ = 81 := by norm_num
    have hf1 : (D.R.f : ℝ) ≤ 81 :=
      ((Real.log_le_iff_le_exp hf0).1 (by linarith : Real.log D.R.f ≤ 4)).trans he4
    have hr1 : (D.R.r : ℝ) ≤ 81 :=
      hrn.trans (((Real.log_le_iff_le_exp (hr0.trans_le hrn)).1
        (by linarith : Real.log ka.n ≤ 4)).trans he4)
    have hfr : (D.R.f : ℝ) * D.R.r ≤ 81 * 81 := mul_le_mul hf1 hr1 hr0.le (by norm_num)
    have hZ2 : Zb D large₂ ≤ 81 * 81 * 2 := by
      unfold Zb
      have := mul_pos hf0 hr0
      nlinarith
    have hC2 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have : (81 * 81 * 2 : ℝ) < 1000 ^ 20 := by norm_num
    linarith
  · unfold lamStar
    have h1 := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    have h2 := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    push_cast at h1 h2
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 = (D.R.f : ℝ) ^ 2 := by ring
    rw [e]
    exact add_nonneg h1 h2
  · intro hj
    unfold WeightFamilies.dimY
    have hp5 : 5 ≤ (D.R.sigW j).1 := by
      show 5 ≤ D.R.k + j - 1
      omega
    have h1 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
      have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp5 (by omega)
      omega
    exact Nat.mul_pos (by omega) (by omega)

end GlobalTheory
