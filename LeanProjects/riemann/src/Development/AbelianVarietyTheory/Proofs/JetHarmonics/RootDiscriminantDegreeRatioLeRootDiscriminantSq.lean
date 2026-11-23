import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem lastPos_L_of_setC {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {large₂ : SizeData₂ D} {X : WeightAlgebra.PJ D B P j}
    {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : WeightAlgebra.SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : wL.LastPos := by
  intro τ i hi1
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold WeightAlgebra.gapZ at h3
  rw [dif_neg hn] at h3
  have hTp : (0 : ℤ) < (WeightAlgebra.Tp D j T : ℤ) := by unfold WeightAlgebra.Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (WeightAlgebra.Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, _root_.one_mul]
    unfold WeightAlgebra.Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  rw [← h3] at h4
  exact_mod_cast h4

theorem rootDiscriminantDegreeRatio_le_rootDiscriminant_sq (D : D7) : rr0 D ≤ D.host.rdE ^ (2 : ℝ) := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := D.host.E)
  have e : D.host.rdE ^ (2 : ℝ) = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [e]
  unfold rr0
  exact div_le_self (by positivity) (by linarith)

theorem runNum_of_sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ), InR D j → ∀ (X : WeightAlgebra.PJ D B P j) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), WeightAlgebra.ParA large₂ H.CA → WeightAlgebra.SetC large₂ X H.CK H.C1 H.A1 ka wL wF Tn nP nW h0 → WeightAlgebra.H3 large₂ H C2 A2 CR 0 wL Tn → PageSupp D large₂ B C2 A2 nW S wL → 2 ≤ CR → RunNum D wL (WeightAlgebra.cc D large₂ C2 A2 CR wL) := by
  intro D large₂ B P j hj X H C2 A2 CR S ka wL wF Tn nP nW h0 hA hS h3 hP hCR
  have h1 := lastPos_L_of_setC hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hn, -, hL, -⟩ := hS
  have hw : wL.n = nW := hL.1
  obtain ⟨hP13, -, -, hr, hD⟩ := hP
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hm : 1 ≤ D.R.m := hj.1.trans hj.2
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hDR : (3 : ℝ) ≤ WeightAlgebra.DF wL := by exact_mod_cast hD
  have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * wL.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    rw [hw]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hP13
  have hq := modulus_pos_of_third_hypothesis h3
  have h31 := h3.1
  rw [Real.rpow_zero, _root_.one_mul] at h31
  have hs : (2 : ℝ) ≤ 2 * D.R.f * D.R.m := by nlinarith
  have hRR : D.host.rdE ^ (2 : ℝ) ≤ WeightFamilies.RRv D CR :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hCR
  have h4 : rr0 D ≤ WeightFamilies.RRv D CR := (rootDiscriminantDegreeRatio_le_rootDiscriminant_sq D).trans hRR
  have hqg : ∀ i, (WeightAlgebra.qq D : ℝ) ≤ D.host.g i := fun i => by
    have : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      exacts [min_le_left _ _, min_le_right _ _]
    exact_mod_cast this
  have r0 : 0 ≤ rr0 D := by unfold rr0; positivity
  generalize hsd : (2 * D.R.f * D.R.m : ℝ) = s at *
  have p0 : (1 : ℝ) ≤ s ^ 4 * wL.n + 2 * s ^ 3 := by
    have a : (0 : ℝ) ≤ s ^ 4 * wL.n := by positivity
    have b : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hR2 : s ^ 2 ≤ WeightFamilies.RRv D CR := by
    refine le_trans ?_ hRR
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith) hrd 2
  have hR1 : 1 ≤ WeightFamilies.RRv D CR := by nlinarith
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := p0.trans h5
  have hkey : s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ WeightAlgebra.qq D := by
    refine le_trans ?_ h31
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc s ^ 2 ≤ WeightFamilies.RRv D CR := hR2
      _ ≤ WeightFamilies.RRv D CR ^ 4 := le_self_pow₀ hR1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hP1)
  refine ⟨h1, ?_, fun i => ?_, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨?_, ?_⟩⟩
  · rw [hw]
    refine le_trans ?_ hn
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  · have a : 4 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have b : 4 * (WeightAlgebra.DF wL : ℝ) + 4 ≤ D.host.g i := by nlinarith [hqg i]
    exact_mod_cast b
  · rw [hsd]
    have a : Real.sqrt s ≤ s := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have b : (WeightAlgebra.DF wL : ℝ) * (2 * Real.sqrt s) ≤ (WeightAlgebra.DF wL : ℝ) * s * 2 := by nlinarith
    have c : (6 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) * s := by nlinarith
    have d := hqg i
    nlinarith
  · rw [hsd]
    have d := hqg i
    unfold WeightAlgebra.cc
    gcongr

end GlobalTheory.PtTie
