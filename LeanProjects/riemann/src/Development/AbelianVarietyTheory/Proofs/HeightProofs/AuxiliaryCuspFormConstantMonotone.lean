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
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCuspStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IInfLeOfCombBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonSectionsOfNoLeadingTerm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

theorem runOK_of_pageOK {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.EtaAn.RunOK D.host.E D.R.r (DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + DF wL))) D.R.m := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 B.KO) B.KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  exact (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j X _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1

theorem small_rows {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    0 ≤ large₂.sc.L ∧ 0 ≤ Zb D large₂ ∧ 0 ≤ cc D large₂ C2 A2 7 wL ∧ OPO large₂ B ∧ 1 ≤ WeightFamilies.PPv D large₂ 200000 2 ∧
      1 ≤ 200000 * zBase large₂ ^ 2 := by
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  obtain ⟨hA, hS, -, -, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hd⟩ := hS
  have hC : 0 ≤ C2 := by have := hd.1; rw [hP.tie.1] at this; linarith
  have hrd : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
  have hL : 0 ≤ large₂.sc.L := by
    by_contra hn
    have h1 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) := by positivity
    have h2 := mul_nonpos_of_nonneg_of_nonpos h1 (not_le.1 hn).le
    unfold zBase at hZ1
    linarith
  refine ⟨hL, le_trans zero_le_one hZ1, ?_, hO, ?_, by nlinarith⟩
  · unfold cc WeightFamilies.RRv WeightFamilies.PPv
    have := Real.rpow_nonneg hrd 7
    have := Real.rpow_nonneg (le_trans zero_le_one hZ1) A2
    positivity
  · unfold WeightFamilies.PPv
    have := Real.one_le_rpow hZ1 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem auxiliaryCuspFormConstant_monotone (D : D7) (j : ℕ) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') : PI4 D j a b ≤ PI4 D j a' b' := by
  unfold PI4
  have : 2 * b / (WeightFamilies.dimY D j : ℝ) ≤ 2 * b' / (WeightFamilies.dimY D j : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_primeData_heights_of
    (hIndef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hDef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hData : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → 0 < wL.n → (j < D.R.m → (recPlus h j hj).NonZeroComp _ G.et) → ∀ (Gc Prw : ℝ) (Tn : ℕ), ∃ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InLiftC S Gc Prw Tn)) :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (T.Q.Xo j) T.Q.c → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus CL hAlg hP hC hCL hLam G hGen hEta hTh hBas hdel hComb
  obtain ⟨hG, hT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨g0, hcur⟩ := GlobalTheory.T.page_hypotheses_at_cusp D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hspl := GlobalTheory.Reg.compSplit_record D T h j hj hG
  have hbirA := fun ka wL wF G => (GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2
  have hbir := hbirA _ _ _ _ hcur.2.1
  obtain ⟨hL, hZ, hc0, hO, hPet, hP16⟩ := small_rows hP
  obtain ⟨hW, hN, hlogN, -, hlow⟩ := hGen
  obtain ⟨-, h3, hn, hn0, hDF, h2, hPO, -, hcg, -⟩ := GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N 1 hj hP hCL hN one_pos hlogN (by
      rw [Nat.cast_one, Real.log_one]; positivity)
  obtain ⟨y, hw, hc, ht, hl⟩ := hData D T h j hj hG (hT hG) ka wL wF
    (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 hcur hinj hspl hbir hbirA hn0
    (fun hjm => (hEta hjm).2.1.2) (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn
  refine ⟨_, hc, ht, hl, ?_⟩
  rcases Nat.eq_zero_or_pos G.del with hd0 | hd0
  · exact GlobalTheory.RunJoin.NoPoint.heights_no_point D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S G _ _ _ _ _ hd0 hBas hc
  have hlc := (GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N G.del hj hP hCL hN hd0 hlogN hdel).1
  have hlN : Real.log G.N + 1 / 2 ≤ prwR large₂ * (wL.size - 1) := by
    have := hW.2.2.1
    unfold prwR
    linarith
  have hW' : G.TiedW S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) :=
    ⟨hW.1, hW.2.1, by linarith, hW.2.2.2⟩
  obtain ⟨-, -, -, hH1, hH2, -, hH4, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, PLam, lNc, hPL, hlNc, hI1, w2, hw2, t2, ht2, hnz2, hs2⟩ := hH4
  have hPI : PI4 D j PLam lNc ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) :=
    (auxiliaryCuspFormConstant_monotone D j hPL hlNc).trans (le_max_right _ _)
  have hsz : (0 : ℝ) ≤ wL.size := by linarith
  have hdm : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
  have hs2' : ∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤
      max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) * (WeightFamilies.dimY D j : ℝ) * wL.size := fun σ =>
    (hs2 σ).trans (by gcongr)
  have hth' : ∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF := fun i => hH2.2.1 (hTh i).1
  have hO2 : Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ PO D large₂ := by
    have hd : (0 : ℝ) < |(NumberField.discr T.Q.c.F : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero T.Q.c.F)
    rw [Real.log_rpow hd, one_div, inv_mul_eq_div]
    exact hO.2
  have hprw : 1 ≤ prwR large₂ := by unfold prwR; linarith
  obtain ⟨hA1, hA2⟩ := GlobalTheory.RunJoin.combAlg_of_tiedW D T h j hj ka wL wF S nus G _ _ _ hW hComb
  rcases lt_or_eq_of_le hj.2 with hjm | hjm
  · obtain ⟨hi, hec, -, hes, hea, hem⟩ := hEta hjm
    obtain ⟨w1, hw1, t1, ht1, hnz1, hs1⟩ := hI1 hjm
    refine hIndef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (cc D large₂ C2 A2 7 wL) (thR wL) w1 t1
      (hn ▸ hw1) ht1 hnz1 (fun σ => (hs1 σ).trans (by gcongr)) hi hem hec.2 hes hc0 hcg (hA1 hjm) hlow hea
  · refine hDef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (hA2 hjm) ?_
    intro σ hσ k x hx
    have h1 := hlow σ hσ k x hx
    have h2 : I2.phiFD ((T.U j σ).X k) (thR wL) x = 0 :=
      GlobalTheory.phiFD_eq_zero_at_last_index D T h j hj hjm _ _ _ (runOK_of_pageOK hP) σ hσ k x hx
    rw [h2, mul_zero, add_zero] at h1
    exact h1

end GlobalTheory.RunPrimeData
