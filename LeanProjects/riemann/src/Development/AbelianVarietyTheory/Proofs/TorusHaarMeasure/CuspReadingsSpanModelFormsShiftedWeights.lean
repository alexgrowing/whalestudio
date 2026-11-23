import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadingsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModelsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem onto_of_page : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∀ k : ℕ, GlobalTheory.Shares.RdOnto h j (addL wF wL k)) ∧ GlobalTheory.Shares.MggOnto h j 7 Tn (cc D large₂ C2 A2 7 wL) ka := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPage
  have hG : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  obtain ⟨hA, hB, -, -⟩ := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hj.1 hPage.hyp
  have key : ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → u.LastPos → GlobalTheory.Shares.RdOnto h j u := fun u hn hl =>
    GlobalTheory.T.cuspForm_families_complex_combination_of_readings GlobalTheory.T.harmonic_germ_value_chart_independent D T h j hj hPar.sh hG hPar.bad hPar.same u hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj u hl)
  refine ⟨fun k => key _ ?_ ?_, ?_⟩
  · have h1 := hB wF (by simp)
    have e : (addL wF wL k).n = wF.n + k * wL.n := rfl
    omega
  · intro τ i hi
    have h1 := (hA wF (by simp)).2.2.2 τ i hi
    have e : (addL wF wL k).aP τ i = wF.aP τ i + k * wL.aP τ i := rfl
    omega
  · refine GlobalTheory.T.vanishing_low_coefficient_readings_span_models D T h j hj ka 7 Tn _ (fun hlt => ?_)
      (key ka (hB ka (by simp)) (hA ka (by simp)).2.2.2)
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hPage.tie
    have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
      ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    obtain ⟨hc, -, -, -, -, h2, h11⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j (recPJ h j hj) _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF
      Tn nP nW h0 hPage.hyp ht hPage.page hlt hj.1 (le_trans (by norm_num) hPage.df)
    have hT : 0 < Tn := by nlinarith
    exact GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients GlobalTheory.T.arithmeticCMKnownTheorems_proof D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hlt (le_trans (by norm_num) hPage.r8)
      (by exact_mod_cast hT) hc

end GlobalTheory.RunJoin
