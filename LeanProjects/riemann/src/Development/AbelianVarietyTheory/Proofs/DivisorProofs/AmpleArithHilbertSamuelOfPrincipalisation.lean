import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionCountGrowthMetricNearGeneratorMaxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyWeightIncrementSemiPositiveCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hx
  have hG := GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := GlobalTheory.T.sectionCount_growth_metric_near_generatorMax hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
