import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunParametersAtRecord

theorem lower_real (R P d a r q : ℝ) (hR : 0 ≤ R) (hd : 1 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (h1 : 90 * (a + 1) ≤ P) (h2 : r ≤ P) (hq : R ^ 4 * P ^ 3 * d ^ 2 ≤ q) :
    R ^ 4 * (90 * (a + d)) * d * r ≤ q := by
  have hP : 1 ≤ P := by linarith
  have e1 : 90 * (a + d) ≤ P * d := by nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ d), mul_le_mul_of_nonneg_left hd ha]
  have e2 : r ≤ P ^ 2 := by nlinarith
  refine le_trans ?_ hq
  have hd0 : 0 ≤ d := by linarith
  have hP0 : 0 ≤ P := by linarith
  calc R ^ 4 * (90 * (a + d)) * d * r ≤ R ^ 4 * (P * d) * d * P ^ 2 := by gcongr
    _ = R ^ 4 * P ^ 3 * d ^ 2 := by ring

theorem run_at_record : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  intro D B P j X K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp ht hPg hSu
  obtain ⟨hA, hS, h3, -, -⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcol, -, hL, -, -, -, -, -, -, h40, -, -, -, hd⟩ := hS
  obtain ⟨hq1, -, -, -, -, hq6⟩ := h3
  rw [Real.rpow_zero, one_mul] at hq1
  obtain ⟨h13, -, hf2, hr8, hDF⟩ := hSu
  have hn : wL.n = nW := hL.1
  have hC1 : H.C1 = C2 := ht.1
  rw [hC1] at hd
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hA2 : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hf := hostSize_f D
  have hrd := hostSize_rd D
  have h16 := EtaleWeightGaps.sixteen_le_rdE_of_parA hA
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  have hf8 := D.eight_le_f
  have hm2 := D.R.two_le_m
  have hRR : WeightFamilies.RRv D CR = I2.RR (E := D.host.E) := by
    rw [hCR]
    unfold WeightFamilies.RRv I2.RR
    rw [hrd]
    exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hRR0 : 0 ≤ I2.RR (E := D.host.E) := by
    unfold I2.RR
    rw [hrd]
    positivity
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have h12 : WeightAlgebra.sizeConstantAtParamsWeight D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    refine le_trans hd.2.2.2.2.2.2.2.2.1 ?_
    unfold WeightFamilies.PPv
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hd.1])
    change zBase large₂ ^ 4 ≤ _
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by push_cast; linarith)
  have h90 : 90 * ((D.R.f : ℝ) * D.R.r + 1) ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h12
  have hf8' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have hr8' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast hr8
  have hDF' : (3 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrP : (D.R.r : ℝ) ≤ WeightFamilies.PPv D large₂ C2 A2 := by nlinarith
  have hq2 : (2 : ℝ) ≤ (qq D : ℝ) := by
    have : (0 : ℝ) ≤ ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) := by positivity
    linarith
  have hq2' : 2 ≤ qq D := by exact_mod_cast hq2
  have hg0 : 2 ≤ D.host.g 0 := le_trans hq2' (min_le_left _ _)
  have hg1 : 2 ≤ D.host.g 1 := le_trans hq2' (min_le_right _ _)
  have hqg : qq D ≤ D.host.g 0 * D.host.g 1 :=
    le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have hqg' : (qq D : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hqg
  have hds : (I2.dstar (E := D.host.E) D.R.m : ℝ) = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by
    unfold I2.dstar
    rw [hf]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, by omega⟩
  · have key := GlobalTheory.RunParametersOfLower.runOK_of_le D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) D.R.m (by omega)
      (by rw [hf]; nlinarith) (by omega) (by rw [hf]; exact_mod_cast hm4) (by rw [hf, hrd]; exact hf2)
      (by rw [hrd]; exact h16)
      (by
        rw [hf]
        rw [hRR] at hq1
        exact lower_real _ _ _ _ _ _ hRR0 (by linarith) (by positivity) (by positivity) h90 hrP (hq1.trans hqg'))
    rw [hf] at key
    exact key
  · unfold cc
    rw [hRR, hds, hn]
    have a1 : 16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h13
    have a0 : 0 ≤ 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 := by positivity
    have a2 : 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := by linarith
    have hP0 : 0 ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans a0 a2
    have a3 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      le_mul_of_one_le_right hP0 (one_le_pow₀ (by linarith))
    refine div_le_div₀ (by positivity) ?_ (by linarith) hqg'
    rw [mul_comm _ (I2.RR (E := D.host.E)), mul_assoc (I2.RR (E := D.host.E))]
    exact mul_le_mul_of_nonneg_left (a2.trans a3) hRR0
  · unfold p14
    rw [hds, hn]
    have g0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
    have g1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
    have g4 : (4 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith
    have b1 : Real.log Real.pi ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_le_four])
    have b0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := Real.log_nonneg (by linarith)
    have hW : (1 : ℝ) ≤ nW := by exact_mod_cast (by omega : 1 ≤ nW)
    have b2 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * nW :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hW
    have b3 := le_mul_of_one_le_left b0 b2
    have e1 : 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) = 4 * D.R.f * D.R.m := by ring
    have e2 : 2 * (D.R.f : ℝ) * (D.R.m : ℝ) / 2 = D.R.f * D.R.m := by ring
    rw [e1, e2]
    linarith

end GlobalTheory.RunParametersAtRecord
