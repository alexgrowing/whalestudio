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
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBoundsStatement

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lieFac_scalar {D : D7} (T : Top D) (j i : ℕ) : lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) = 1 := by
  have : ∀ x, wtA (wEt D j i) x = 0 := by
    intro x
    simp [wtA, wEt, WeightAlgebra.wscalar, ext0]
  simp [lieFac, this]

theorem weight_add_eq_smul_of_G2 {D : D7} {j : ℕ} {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wadd wF w2 = wsmul (WeightFamilies.dimY D j + 4) wL := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold wadd wsmul
  congr 1
  · funext τ i; rw [add_comm]; exact h2 τ i
  · funext τ i; rw [add_comm]; exact h3 τ i
  · rw [add_comm]; exact h1

theorem thR_pos {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hg : ∀ i, 0 < D.host.g i) (hd : 0 < DF w) : 0 < thR w := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _
  have h0 := hg 0
  have h1 := hg 1
  unfold thR I2.th I2.RR
  positivity

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem curveHyp_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hP
  obtain ⟨hT, hN, hlN, hZ, hLow⟩ := hGen
  have hZb : 0 ≤ Zb D large₂ := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact le_trans (by positivity) hd.2.1
  have hC2 : 0 ≤ C2 := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := hd.1
    rw [hP.tie.1] at this
    linarith
  have hrow := (GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds D _ _ j (recPJ h j hj) large₂ H C2 A2 CT ka wL wF Tn nP nW h0 1 G.N 1 hj hP one_pos hN one_pos hlN
    (by rw [Nat.cast_one, Real.log_one]; positivity)).2.2.2.2.2.2.2.2.1
  have hc0 : 0 ≤ cc D large₂ C2 A2 7 wL := by
    have h1 : 0 ≤ zBase large₂ := hZb
    have h2 : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
    unfold cc WeightFamilies.RRv WeightFamilies.PPv
    positivity
  obtain ⟨hsz, PL, lN, -, -, hI1, w2, hw2, th2, -, hth2, -⟩ :=
    (FamilyHypotheses.fourthHypothesis_iff_sizes_and_index large₂ (recPJ h j hj) H C2 A2 7 ka wL wF Tn nW).1 hC.2.2.2.2.2.2.1
  have hth : 0 < thR wL := thR_pos wL (fun i => lt_of_le_of_lt (Nat.zero_le _) (hsz.2.2.2.2.2 i))
    (lt_of_lt_of_le (by norm_num) hP.df)
  refine ⟨g0, hT.1, ?_, ⟨WeightFamilies.dimY D j + 4, w2, th2, weight_add_eq_smul_of_G2 hw2, (hnz w2 th2 hth2).1⟩, hg0⟩
  refine GlobalTheory.T.set_constants_good_embedding_recursion D T h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj))
    (cc D large₂ C2 A2 7 wL) large₂ H.CK H.C1 H.A1 h0 Tn nP nW hP.hyp.2.1 hZ (fun hjm => ?_) hc0 (by linarith) (fun hjm => ?_)
  · obtain ⟨hi, hcu, -, -, hA, -⟩ := hEta hjm
    refine ⟨hi, hcu.2, T.σ₀, T.toCore.good_σ₀, ?_⟩
    have e : Fin (G.N - 1 + 1) ≃ Fin G.N := finCongr (by omega)
    refine GlobalTheory.BigRec.phRec_of_firstMin D T h j hj T.σ₀ wL G.N (G.N - 1) G.iet G.w e G.et (thR wL) (p14R wL) (DF wL)
      (200000 * zBase large₂ ^ 2) _ T.toCore.good_σ₀ hth (fun σ hσ k x hx => ?_) hZ (fun k x hx => ?_)
    · have h1 := hLow σ hσ k x hx
      rw [← e.sum_comp] at h1
      exact h1
    · have h1 := hA T.σ₀ T.toCore.good_σ₀ k x hx
      rw [lieFac_scalar, one_mul] at h1
      exact h1
  · obtain ⟨w1, hw1, th1, -, hth1, -⟩ := hI1 hjm
    exact ⟨w1, hw1, th1, hth1⟩

end GlobalTheory.RunJoin
