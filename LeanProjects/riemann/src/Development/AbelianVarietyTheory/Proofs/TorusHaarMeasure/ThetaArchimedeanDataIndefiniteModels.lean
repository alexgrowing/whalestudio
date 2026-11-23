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
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjCmHalfIntegralGeneratorEqOneSub
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem thR_pos_of_rank {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hr : 0 < D.R.r) : 0 < thR w := by
  have hf : 0 < D.R.f := GlobalTheory.ArchInputs.f_pos D
  have hfE : I2.PT.f D.host.E = D.R.f := GlobalTheory.ArchInputs.finrank_host D
  have hrd := GlobalTheory.ArchInputs.one_le_rd (E := D.host.E)
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  unfold thR I2.th I2.RR
  rw [hfE]
  positivity

theorem sq_le_of_mul_le_exp {a b i p q : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h : a * b ≤ Real.exp (-i * (p - q))) :
    b ^ 2 ≤ Real.exp (2 * (i * q)) / a ^ 2 * Real.exp (-(2 * i * p)) := by
  have h2 := pow_le_pow_left₀ (mul_nonneg ha.le hb) h 2
  rw [← Real.exp_nat_mul] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← Real.exp_add, ← mul_pow, mul_comm b]
  refine h2.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem archAt_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → Nonempty (GlobalTheory.Shares.ArchAt h j G.w wF Tn (WeightFamilies.c1 D 7 Tn (cc D large₂ C2 A2 7 wL) j)) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus _ hP hC hjm G hGen hEta
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨n1, n2, n3, n4, -, n6, -⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j _ _ 1 4 0 11 large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp ht hP.page hjm hj.1 (le_trans (by norm_num) hP.df)
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, PLam, lNc, -, -, hw1, w2, hG2, th2, -, hth2, -⟩, -⟩ := hC
  obtain ⟨w1, hG1, th1, -, hth1, -⟩ := hw1 hjm
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0
    (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hP
  obtain ⟨-, -, -, hw, hlow⟩ := hGen
  obtain ⟨hi, ⟨-, het⟩, -, -, harch, -⟩ := hEta
  have hth : 0 < thR wL := thR_pos_of_rank wL (lt_of_lt_of_le (by norm_num) hP.r8)
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hP.hyp hP.page hP.ck).1
  have hL : 2 ≤ large₂.sc.L := by
    obtain ⟨_, _, hsz, -⟩ := hP.page
    exact (GlobalTheory.EtaAn.page_rows D large₂ _ hP.hyp.1 hsz).1
  have hrn : D.R.r ≤ ka.n := ((GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj.1
    hP.hyp).1 ka (by simp)).2.2.1
  refine GlobalTheory.ArchInputs.archAt_nonempty D T h j hj large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 7 _ G.N G.w G.iet G.et w1 w2
    th1 th2 hP.hyp hjm hP.r8 n1 n2 n3 n4 n6 hi hG1 hG2
    (fun k x hx => GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx)
    ((hnz _ G.et het).2 T.σ₀ T.good_σ₀) ((hnz _ th1 hth1).2 T.σ₀ T.good_σ₀) ((hnz _ th2 hth2).2 T.σ₀ T.good_σ₀)
    (fun k => ⟨g0, (hnz _ g0 hg0).2 T.σ₀ T.good_σ₀ k⟩) (fun k => ?_) (fun k => ?_)
    (GlobalTheory.ExtraWeight.extra_weight_exists D T h j hj large₂ ka (GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore) hrows hL hrn hjm
      hP.frd (sixteen_le_rdE_of_parA hP.hyp.1) (by exact_mod_cast lift_index_pow_four_le_degree hP.page))
  · refine ⟨thR wL, Real.exp (2 * (p14R wL * (DF wL : ℝ))) * lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2, hth,
      fun x hx => ?_⟩
    have h1 := hlow T.σ₀ T.good_σ₀ k x hx
    have hs : ∑ m, recNrm (T.U j T.σ₀) (xiR D) (wtA wL) wL.n (G.w m).1 k x ^ 2 =
        lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2 *
          ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]; rfl
    have hpos : 0 < ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (GlobalTheory.BigRec.pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    rw [hs] at h1
    have h2 := GlobalTheory.BigRec.exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos _ _ _) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · refine ⟨thR wL, _, hth, fun x hx => sq_le_of_mul_le_exp (lieFac_pos _ _ _) ?_ (harch T.σ₀ T.good_σ₀ k x hx)⟩
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)

end GlobalTheory.RunJoin
