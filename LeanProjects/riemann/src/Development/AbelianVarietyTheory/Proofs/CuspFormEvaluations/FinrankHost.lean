import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

theorem finrank_host (D : D7) : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  push_cast
  ring

theorem discr_rpow (D : D7) :
    |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f) = D.host.rdE ^ 2 := by
  have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  unfold Host.rdE
  rw [finrank_host, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  field_simp

theorem two_le_dimY (D : D7) {j : ℕ} (hj : j < D.R.m) (h1 : 1 ≤ j) : 2 ≤ WeightFamilies.dimY D j := by
  have hf : 8 ≤ D.R.f := D.eight_le_f
  have hk := D.R.m_add_three_le_k
  have hp : 1 ≤ (D.R.sigW j).1 := by unfold Ranks.sigW; simp only; omega
  have hq : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpq : 1 ≤ (D.R.sigW j).1 * (D.R.sigW j).2 := Nat.mul_pos hp hq
  unfold WeightFamilies.dimY
  calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hf (by omega)

theorem core (r f m ρ rd PP c T g DF q : ℝ) (hg : g = 1250 * r) (hr : 0 ≤ r) (hrT : r ≤ T) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ m) (hrd : 2 * f * m ≤ rd) (hPP : 0 < PP) (hq : 0 < q)
    (hc : c = rd ^ 7 * PP * DF ^ 2 / q) (hql : (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 ≤ q) (hgP : g * f * m ^ 3 ≤ PP ^ 2) :
    r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) ≤ 2 * T := by
  have h2f : 2 * f ≤ rd := by nlinarith
  have hrd1 : 1 ≤ rd := by linarith
  have hT : 0 ≤ T := hr.trans hrT
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcP : c * (PP ^ 2 * rd ^ 21) ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one hq]
    calc _ = (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := hql
  have e : r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) =
      r + T * (c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9))) := by
    rw [hg]; field_simp; ring
  have a1 : g * f * ρ ^ 3 ≤ PP ^ 2 := by
    refine le_trans ?_ hgP
    have : 0 ≤ g * f := by rw [hg]; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρ 3) this
  have a2 : 2 * f * rd ^ 9 ≤ rd ^ 21 := by
    calc 2 * f * rd ^ 9 ≤ rd * rd ^ 9 := mul_le_mul_of_nonneg_right h2f (by positivity)
      _ = rd ^ 10 := by ring
      _ ≤ rd ^ 21 := pow_le_pow_right₀ hrd1 (by norm_num)
  have a3 : (g * f * ρ ^ 3) * (2 * f * rd ^ 9) ≤ PP ^ 2 * rd ^ 21 :=
    mul_le_mul a1 a2 (by positivity) (by positivity)
  have a4 : c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9)) ≤ 1 := (mul_le_mul_of_nonneg_left a3 hc0).trans hcP
  rw [e]
  have := mul_le_mul_of_nonneg_left a4 hT
  linarith

theorem numbers : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → j < D.R.m → 1 ≤ j → 1 ≤ WeightAlgebra.DF wL → 0 < WeightAlgebra.cc D large₂ C2 A2 CR wL ∧ (Tn : ℝ) * WeightAlgebra.cc D large₂ C2 A2 CR wL * g0 D ≤ 1 ∧ 1 ≤ WeightFamilies.RRv D K.CRm ∧ (D.R.r : ℝ) * (1 + WeightFamilies.c1 D K.CRm Tn (WeightAlgebra.cc D large₂ C2 A2 CR wL) j / (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) ≤ 2 * Tn ∧ addL wF wL Tn = ka ∧ 2 ≤ WeightFamilies.dimY D j ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn := by
  intro D B P j X K Ch Ah Cq Aq large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hH ht hPg hj h1 hDF
  obtain ⟨hA, hS, h3, -, -⟩ := hH
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hL, hF, -, -, -, -, hrT, -, -, h11, -, hd⟩ := hS
  have hgP := g0fm3_le_of_dom hPg ht hd
  obtain ⟨e1, e2, e3⟩ := tie_eqs ht
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hK : K.CRm = 7 := ht.2.2.2.2.2.2.1
  have hrd16 := sixteen_le_rdE_of_parA hA
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hRR : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
    unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hC : 1000 ≤ C2 := ht.1 ▸ hd.1
  have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have := WeightFamilies.one_le_zBase large₂
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hql, -, -, hTc, -, -⟩ := h3
  rw [Real.rpow_zero, one_mul, hCR, hRR] at hql
  rw [e1, e2, e3] at hTc
  have hDF' : (1 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrd0 : 0 < D.host.rdE := by linarith
  have hq : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by positivity) hql
  have hc : WeightAlgebra.cc D large₂ C2 A2 CR wL = D.host.rdE ^ 7 * WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 / (qq D : ℝ) := by
    unfold WeightAlgebra.cc; rw [hCR, hRR]
  refine ⟨by rw [hc]; positivity, hTc, ?_, ?_, ?_, two_le_dimY D hj h1, h11⟩
  · rw [hK, hRR]; exact one_le_pow₀ (by linarith)
  · rw [discr_rpow]
    unfold WeightFamilies.c1 WeightFamilies.dP
    rw [hK, hRR]
    push_cast
    have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    refine core _ _ (D.R.m : ℝ) _ _ _ _ _ (g0 D : ℝ) _ _ ?_ (Nat.cast_nonneg _) ?_ (by linarith) (by linarith)
      (Nat.cast_nonneg _) ?_ hrd hPP hq hc hql hgP
    · unfold g0; push_cast; norm_num
    · exact_mod_cast (by omega : D.R.r ≤ Tn)
    · have : WeightFamilies.rho D j ≤ D.R.m := by unfold WeightFamilies.rho Ranks.sigW; simp only; omega
      exact_mod_cast this
  · obtain ⟨f1, f2, f3⟩ := hF
    have l1 := hL.1
    obtain ⟨aP, aM, p1, p2, n, p3⟩ := ka
    unfold addL wadd wsmul
    simp only [WeightFamilies.Wt.mk.injEq]
    simp only at hn f2 f3
    refine ⟨?_, ?_, ?_⟩
    · funext τ i
      have := f2 τ i
      zify; linarith
    · funext τ i
      have := f3 τ i
      zify; linarith
    · rw [f1, l1, hn, hnV]

end GlobalTheory.ExtraWeight
