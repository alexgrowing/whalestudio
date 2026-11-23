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
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaleExtensionDegreeTwoConstantsStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtValIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.EtaBoundForm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_etaOK : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → ∃ (i : ℕ) (et : (recB h.toLawsCore).Cusp j (etWt D j i)), EtaOK h j hj large₂ wL i et := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm
  obtain ⟨Q, PT, hS, -, -⟩ := id hP.page
  have what₂ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hP.hyp.1 hS
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO)) : (recB h.toLawsCore).KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 (recB h.toLawsCore).KO) (recB h.toLawsCore).KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO)) : (recB h.toLawsCore).KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  have hrun := (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j (recPJ h j hj) _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1
  have hq1 : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlog : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 70 * large₂.sc.L := by
    have a0 : D.host.g 0 ≠ 0 := fun e => by simp [e] at hq1
    have a1 : D.host.g 1 ≠ 0 := fun e => by simp [e] at hq1
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a0) (by exact_mod_cast a1)]
    have b0 := what₂.2.2.2.2.1 0
    have b1 := what₂.2.2.2.2.1 1
    linarith [what₂.1]
  obtain ⟨i, hi, η, ha, hb, hc, hd⟩ := GlobalTheory.T.etaleExtension_degreeTwo_constants D T h large₂ what₂ _ _ _ hrun hq1 hlog j hj.1 hjm
  exact ⟨i, η, hi, ha, hb, hc, hd, ((GlobalTheory.EtaInt.etVal_integral D T h j hj i η).2.2 hb).2⟩

end GlobalTheory.EtaBoundForm
