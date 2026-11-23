import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem three_le_dimY_of_rank (D : D7) (j : ℕ) (hj : InR D j) (hr : 8 ≤ D.R.r) : 3 ≤ WeightFamilies.dimY D j := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  unfold WeightFamilies.dimY
  generalize (D.R.sigW j).1 = a at hs ⊢
  generalize (D.R.sigW j).2 = b at hs ⊢
  have key : ∀ c : ℕ, 3 ≤ c → 3 ≤ c * (c - 1) / 2 := fun c hc => by
    have : 3 * 2 ≤ c * (c - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have h3 : 3 ≤ a * b + a * (a - 1) / 2 + b * (b - 1) / 2 := by
    rcases le_or_gt 3 a with h | h
    · have := key a h; omega
    · have := key b (by omega); omega
  calc 3 = 1 * 3 := rfl
    _ ≤ _ := Nat.mul_le_mul hf h3

theorem DF_add_one_le_size {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) + 1 ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  push_cast at h2 ⊢
  linarith

theorem lamConst_lamR_rows : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 CL N del hj hP hCL hN hdel hlN hld
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hPO : 1 ≤ PO D large₂ := by
    unfold PO
    have h1 : 0 ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * large₂.sc.L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hL
    nlinarith
  obtain ⟨-, hS, h3, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIL, -, -, -, -, h40, -, h22, -⟩ := hS
  obtain ⟨-, -, -, hc, -⟩ := h3
  obtain ⟨-, -, t1, t2, t3, -⟩ := hP.tie
  rw [t1, t2, t3] at hc
  have hdf : (3 : ℝ) ≤ DF wL := by exact_mod_cast hP.df
  have hsz := DF_add_one_le_size wL
  have hn : wL.n = nW := hIL.1
  refine ⟨?_, three_le_dimY_of_rank D j hj hP.r8, hn, by omega, by linarith, by linarith, hPO,
    WeightFamilies.one_le_zBase large₂, ?_, le_max_right _ _⟩
  · set n : ℕ := 8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊) with hndef
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (by rw [hndef]; positivity)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs1 : (wsmul n wL).size ≤ (n : ℝ) * wL.size :=
      GlobalTheory.RunWeights.size_le_mul _ _ n hn1 (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl
    have hs0 : 1 ≤ (wsmul n wL).size := by
      have := DF_add_one_le_size (wsmul n wL)
      have h0 : (0 : ℝ) ≤ DF (wsmul n wL) := Nat.cast_nonneg _
      linarith
    have hP0 : 0 ≤ WeightFamilies.PP0v D large₂ CL 2 := by
      unfold WeightFamilies.PP0v
      rw [Real.rpow_two]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdel' : (0 : ℝ) < del := by exact_mod_cast hdel
    have hceil : (1 : ℝ) + (⌈PO D large₂⌉₊ : ℝ) ≤ 2 + PO D large₂ := by
      have := Nat.ceil_lt_add_one (a := PO D large₂) (by linarith)
      linarith
    have hd0 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) * (N : ℝ) ^ 2 * del := by
      rw [hndef]
      push_cast
      calc 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 1) * del * (1 + (⌈PO D large₂⌉₊ : ℝ))
          ≤ 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 2) * del * (2 + PO D large₂) := by
            gcongr; norm_num
        _ = _ := by ring
    have hA : (0 : ℝ) < 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) := by positivity
    have hlogn := Real.log_le_log (by linarith) hnle
    rw [Real.log_mul (by positivity) hdel'.ne', Real.log_mul hA.ne' (by positivity), Real.log_pow] at hlogn
    push_cast at hlogn
    have hlogs := Real.log_le_log (by linarith) hs1
    rw [Real.log_mul (by linarith) (by linarith)] at hlogs
    have hl0 : 0 ≤ Real.log (wsmul n wL).size := Real.log_nonneg hs0
    have hmain : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (wsmul n wL).size) ≤ lamR large₂ CL wL := by
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hP0
    have hlam : 0 ≤ lamR large₂ CL wL := le_trans zero_le_one (le_max_left _ _)
    unfold LamConst
    rw [mul_assoc (lamR large₂ CL wL)]
    exact mul_le_mul hmain hs1 (by linarith) hlam
  · have hT : (2 : ℝ) ≤ Tn := by
      have : 2 ≤ Tn := by omega
      exact_mod_cast this
    rw [mul_assoc] at hc
    by_contra hcon
    push Not at hcon
    nlinarith

end GlobalTheory.RunJoin
