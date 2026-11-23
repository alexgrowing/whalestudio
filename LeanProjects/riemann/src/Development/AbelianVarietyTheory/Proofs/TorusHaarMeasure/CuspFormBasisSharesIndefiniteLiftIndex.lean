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
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.H2XNIffH2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsInBasisSharesInContain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModelsStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeightsStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : RunIn.SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

def ownNorm (B : WeightFamilies.Prov D) : RunIn.SecNorm B :=
  ⟨B.l2NormAlt, B.l2Norm_nonneg_bis, B.l2Norm_eq_zero_iff, B.l2Norm_smul_alt, B.l2Norm_add_le', B.l2Norm_le_supNorm_alt⟩

set_option maxHeartbeats 400000 in

theorem sharesAt_ownNorm {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (Sh : Set (B.Cusp j wF)) :
    SharesAt (RunIn.globalFamilyDataBaseChange (ownNorm B) X E hM G) (scalarsWithNorm (ownNorm B).N (ownNorm B).h0 (ownNorm B).h1 (ownNorm B).h2
      (ownNorm B).h3 (ownNorm B).h4 S) Tn c Sh ↔ SharesAt (gd2Xplus G E hM) S Tn c Sh :=
  Iff.rfl

set_option maxHeartbeats 400000 in

theorem sharesAt_of_xplus {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (Sh : Set (B.Cusp j wF)) (h : SharesAt (gd2Xplus G E hM) S Tn c Sh) : SharesAt G S Tn c Sh := by
  obtain ⟨del, th', h1, h2⟩ := h
  refine ⟨del, th', h1, fun rz alz th0 zc rq th iet et => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := h2 rz alz th0 zc rq th iet et
  exact ⟨fun la => a la, b, c, d, fun la => e la⟩

set_option maxHeartbeats 4000000 in

theorem shortG_xN (wL wF : WeightFamilies.Wt D j) (S : Scal B) (β : ℝ) :
    ShortG (RunIn.xN n X E hM) ((RunIn.xN n X E hM).wF0 wL wF)
      ((RunIn.xN n X E hM).Thc (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S).s0 ((RunIn.xN n X E hM).wF0 wL wF)) β ↔
    ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) β :=
  Iff.rfl

end General

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem sharesAt_of_lt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → LatAt (recB h.toLawsCore) j ka → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → SharesAt G S Tn (cc D large₂ C2 A2 7 wL) Sh := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus hPar hPg hH hLat hjm G hG hE Sh hSh
  have ht : TieC (⟨1,2,1,2,1,2,1,4,7⟩ : KAdm) H 1 4 0 11 C2 A2 7 := by
    obtain ⟨a, b, c, d, e, f⟩ := hPg.tie
    exact ⟨a, b, c, d, e, rfl, rfl, f, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨-, -, -, -, hadd, h2, h11⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j (recPJ h j hj) _ 1 4 0 11 large₂ H C2 A2 7 CT
    ka wL wF Tn nP nW h0 hPg.hyp ht hPg.page hjm hj.1 (le_trans (by norm_num) hPg.df)
  have hA := GlobalTheory.T.thetaArchimedeanData_indefiniteModels D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus hPar hPg hH hjm G hG hE
  obtain ⟨hR, hMg⟩ := GlobalTheory.T.cuspReadings_span_model_forms_shifted_weights D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPg
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PL, -, -, -, hS0, -⟩, -⟩ := hH
  let n := ownNorm (recB h.toLawsCore)
  refine sharesAt_of_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G S Tn _ Sh
    ((sharesAt_ownNorm (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G S Tn _ Sh).1 ?_)
  exact GlobalTheory.Shares.exists_inBasis_shares_inContain D T h j hj n ka wL wF
    (RunIn.globalFamilyDataBaseChange n (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G) Tn 7 (cc D large₂ C2 A2 7 wL)
    (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) hadd h2 h11 hA hR hMg hLat
    ⟨_, (shortG_xN n (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) wL wF S _).2 hS0⟩ Sh hSh

end GlobalTheory.RunJoin
