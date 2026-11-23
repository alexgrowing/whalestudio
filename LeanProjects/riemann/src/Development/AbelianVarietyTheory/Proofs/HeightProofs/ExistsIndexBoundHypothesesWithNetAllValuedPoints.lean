import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharactersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedBoundForRunScalarsStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditionsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditionsStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralFormsLogSupNormLowerBoundAbsoluteStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageBoundPolynomialDomination
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBoundsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBoundStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesIndefiniteLiftIndexStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesDefiniteLiftIndexStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InputsAtRecord

section Transfer

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (E : PtExt X) (hM : IntAtExt X E)
  {ka wL wF : WeightFamilies.Wt D j}

theorem baseIn_xplus {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {S : Scal B} {Tn nP nW : ℕ}
    {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus) :
    BaseIn large₂ (xplus X E hM) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := h

theorem famIn_xplus {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} {S : Scal B} {Tn : ℕ}
    {G : GlobalFamilyData X ka wL wF} {Gc PH Prw Pet Pd : ℝ} (h : FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd) :
    FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn (gd2Xplus G E hM) Gc PH Prw Pet Pd := h

end Transfer

theorem tiedW_mono_count {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    {G : GlobalFamilyData X ka wL wF} {S : Scal B} {Gc a b : ℝ} (hab : a ≤ b) (hW : G.TiedW S Gc a) : G.TiedW S Gc b :=
  ⟨hW.1, hW.2.1, hW.2.2.1.trans (mul_le_mul_of_nonneg_right hab (sub_nonneg.2 wL.one_le_size)), hW.2.2.2⟩

theorem genOK_refill {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (c : ℝ) (hG : GenOK h j hj large₂ G S c)
    (del th' rz alz th0 zc rq th iet et) :
    GenOK h j hj large₂ (FamilyHypotheses.refill G del th' rz alz th0 zc rq th iet et) S c := hG

theorem tiedEt_of_etaOK {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (hE : j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) : G.TiedEt large₂ 200000 2 :=
  fun hlt => ⟨(hE hlt).1, (hE hlt).2.1.1, (hE hlt).2.1.2, (hE hlt).2.2.2.1⟩

theorem exists_gen_eta (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ)
    (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hO : GlobalTheory.PtTie.Oriented T EX) (hP : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0) :
    ∃ G : GlobalFamilyData (recPJ h j hj) ka wL wF,
      GenOK h j hj large₂ G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) ∧
      (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_admissible_thetaLatticeGenerators D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hO hP
  by_cases hlt : j < D.R.m
  · obtain ⟨i, et, hE⟩ := GlobalTheory.T.exists_scalarWeight_auxiliaryForm_of_runConditions D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hlt
    exact ⟨FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et,
      genOK_refill h j hj large₂ G _ _ hG _ _ _ _ _ _ _ _ _ _, fun _ => hE⟩
  · exact ⟨G, hG, fun h' => absurd h' hlt⟩

theorem sharesAt_all (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore))
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hPar : ParOK T EX p j)
    (hP : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hH : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus) (hLat : LatAt (recB h.toLawsCore) j ka)
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (hG : GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL))
    (hE : j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) (Sh : Set ((recB h.toLawsCore).Cusp j wF))
    (hSh : Submodule.span (recB h.toLawsCore).KO Sh = ⊤) : SharesAt G S Tn (cc D large₂ C2 A2 7 wL) Sh := by
  rcases lt_or_eq_of_le hj.2 with hlt | heq
  · exact GlobalTheory.T.cuspFormBasisShares_indefinite_liftIndex D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus hPar hP hH hLat hlt G hG (hE hlt) Sh hSh
  · subst heq
    exact GlobalTheory.T.cuspFormBasisShares_definite_liftIndex D T h EX p hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hPar hP hH hLat G hG.2.2.2.1 Sh hSh

theorem inputsNet_recPlus : ∃ (CL : ℝ) (Cq Z₀ : ℝ → ℝ → ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → Z₀ H.CA H.CK ≤ zBase large₂ → InputsNet large₂ (recPlus h j hj) (kR CL) H 1 4 (Cq H.CA H.CK) 4 C2 A2 7 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL := by
  obtain ⟨CL, hCL, hLam⟩ := GlobalTheory.T.integralForms_logSupNorm_lower_bound_absolute
  obtain ⟨Cq, hQ⟩ := GlobalTheory.T.recursive_page_lattice_bound
  obtain ⟨Z₀, hZ⟩ := GlobalTheory.RunNum.polyDom_of_pageOK CL Cq hCL
  refine ⟨CL, Cq, Z₀, ?_⟩
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hPar hP hZ0
  obtain ⟨hH, hLat, -, hSupp, Sh, hSh, hTh⟩ :=
    GlobalTheory.T.runHypotheses_formsScalars_of_parameterConditions D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hPar hP
  refine ⟨?_, hSupp⟩
  obtain ⟨G₁, hG₁, hE₁⟩ := exists_gen_eta D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hPar.orient hP
  obtain ⟨del, th', hth', hsh⟩ := sharesAt_all D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ _ hPar hP hH hLat
    G₁ hG₁ hE₁ _ hSh
  obtain ⟨hBas, hRd, hRho, hRhoP, hCont⟩ := hsh G₁.rz G₁.alz G₁.th0 G₁.zc G₁.rq G₁.th G₁.iet G₁.et
  have hG := genOK_refill h j hj large₂ G₁ _ _ hG₁ del th' G₁.rz G₁.alz G₁.th0 G₁.zc G₁.rq G₁.th G₁.iet G₁.et
  generalize hGdef : FamilyHypotheses.refill G₁ del th' G₁.rz G₁.alz G₁.th0 G₁.zc G₁.rq G₁.th G₁.iet G₁.et = G at hBas hRho hCont hG
  have hE : j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et := by subst hGdef; exact hE₁
  have hTh' := hTh G (by subst hGdef; exact hth')
  have hdel : G.del = del := by subst hGdef; rfl
  rw [← hdel] at hRd
  obtain ⟨hComb, hc⟩ := GlobalTheory.T.combinedBound_for_runScalars GlobalTheory.T.hodgeTate_inclusion_chart_characters D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hPar.orient hP G hE
  obtain ⟨Nt, σ₀, hMax, hSup, hPG, hInj, hCard, hSub, -, hlog⟩ :=
    GlobalTheory.RunJoin.net_at_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hLam' := hLam D T h large₂ H.CA hP.hyp.1 j
  have hQf := GlobalTheory.T.exists_primeData_curve_lifting_heightBounds D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ _ CL hPar.alg hP hH hCL hLam' G hG hE hTh' hBas
    (hlog G.del hLat hRd) hComb
  obtain ⟨hGq, hPoly⟩ := hZ D _ _ j (recPJ h j hj) large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP hZ0
  have hBase : BaseIn large₂ (recPJ h j hj) (kR CL) H 1 4 (Cq H.CA H.CK) 4 C2 A2 7 CT
      (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) :=
    ⟨hH, hLat, hLam' ka, fun hlt => hQ D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hlt hLat, hSub⟩
  have hFam : FamIn large₂ (kR CL) H 1 4 (Cq H.CA H.CK) 4 C2 A2 7 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Tn G
      (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) (pdR large₂ ka) :=
    ⟨tiedW_mono_count (by unfold prwR; linarith) hG.1, hTh', tiedEt_of_etaOK h j hj large₂ G hE, le_rfl, growthConstantBound_gcR large₂ _, hGq,
      hRd, hRho, hRhoP, hPoly, hBas, hCont⟩
  have hComb' := combBound_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)
    (fun {wL} {n} gens => NoCommonZero (T.Q.Xo j) T.Q.c fun i => (gens i).1)
    G _ _ hc.le _ hG.1.1 hG.2.2.2.1 (fun la _ ha => Formalism.L2.Pj.vAdd_int_nonneg la ha) hComb (regularity_R2_extended_points h j hj)
  exact ⟨baseIn_xplus (extAll h j hj) (intAtExt_extAll h j hj) hBase,
    gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj), _, _, _, _, _, ⟨Nt, σ₀, hMax, hSup, hPG, hInj, hCard⟩,
    famIn_xplus (extAll h j hj) (intAtExt_extAll h j hj) hFam, hComb', hQf⟩

end GlobalTheory.InputsAtRecord
