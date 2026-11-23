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
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetDataExists
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeepSubMulRecAll
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRelationDegThree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem net_count_dim {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j} (Nt : NetNorms.NetData B j ka)
    (σ : B.KO →+* ℂ) (c : ℝ) (hM : NetNorms.NetMax Nt) (hS : NetNorms.NetSize Nt c) (hI : NetNorms.NetInj Nt σ) :
    Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c ∧ ∀ n : ℕ, n ≤ Module.finrank B.KO (B.Cusp j ka) → Real.log n ≤ c := by
  have hlog16 : ∀ k : ℕ, Real.log (k : ℝ) ≤ Real.log (16 * (k : ℝ)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      exact Real.log_le_log hk' (by linarith)
  have hfirst : Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c := (hlog16 _).trans (hS σ)
  refine ⟨hfirst, ?_⟩
  intro n hn

  have hdim : Module.finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hli := hI _ (Module.finBasis B.KO (B.Cusp j ka)) (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have hle := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hle
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hc : 0 ≤ Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Nt.NN σ)) with h0 | h0
      · rw [h0]
        simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ Fintype.card (Nt.NN σ) := by exact_mod_cast h0
        linarith
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [hS σ]
  · calc Real.log (n : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := by
          apply Real.log_le_log (by exact_mod_cast hnpos)
          exact_mod_cast hn.trans hdim
      _ ≤ c := hfirst

theorem le_finrank_of_shareRd {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 B.KO) (B.Cusp j ka)) (Tn del : ℕ) (hT : WeightFamilies.dimY D j + 1 ≤ Tn)
    (hR : ShareRd (D := D) (j := j) Tn del (X.rk ka N)) : del ≤ Module.finrank B.KO (B.Cusp j ka) := by
  have hpos : 0 < Nat.choose (Tn - 1) (WeightFamilies.dimY D j) := Nat.choose_pos (by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) := by exact_mod_cast hpos
  have hR' : (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ (X.rk ka N : ℝ) := hR
  have hdel0 : (0 : ℝ) ≤ del := by positivity
  have hdel : (del : ℝ) ≤ (X.rk ka N : ℝ) := by nlinarith

  have hrk : X.rk ka N ≤ Module.finrank B.KO (B.Cusp j ka) := Submodule.finrank_le _
  have hdel' : del ≤ X.rk ka N := by exact_mod_cast hdel
  exact hdel'.trans hrk

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem net_at_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hyp, page, _tie, _p13, _frd, r8, _df, ck⟩ := hP
  obtain ⟨hrows, hf⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hyp page ck
  obtain ⟨hParA, hSetC, -, -, -⟩ := hyp
  obtain ⟨_Q, _PT, hSz, -, -⟩ := page
  obtain ⟨hL2, -⟩ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hParA hSz
  obtain ⟨hkn, -, -, -, -, -, -, -, -, hnP, -, -, -, hnV, -, -, -, -, -, h40, -⟩ := hSetC
  have hfr : D.R.r ≤ D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
  have hr : D.R.r ≤ ka.n := by
    rw [hkn, hnV]
    have : D.R.f * D.R.r ≤ 8 * D.R.f * D.R.r := by
      rw [Nat.mul_assoc]
      omega
    omega
  have hZ : 1 ≤ Zb D large₂ := by
    have hf' : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hr' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast r8
    have hfr' : (128 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    show 1 ≤ (D.R.f : ℝ) * D.R.r * large₂.sc.L
    nlinarith
  obtain ⟨Nt, hM, hLe, hS, hI⟩ := GlobalTheory.RunIn.NetAtRecord.netData_exists D T h
    (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ j hj ka hrows hL2 hr hf
  let σ₀ : (recB h.toLawsCore).KO →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ)).toRingHom
  obtain ⟨hcnt, hdim⟩ := net_count_dim Nt σ₀ _ hM hS (hI σ₀)
  have hpg := GlobalTheory.page_relation_deg_three D large₂ j ka 1041 3 le_rfl le_rfl hZ
  refine ⟨Nt, σ₀, hM, hLe, fun σ => (hS σ).trans hpg, hI σ₀, hcnt.trans hpg,
    (GlobalTheory.deepSubMul_rec_all D T h j hj).1, hdim _ le_rfl, ?_⟩
  intro del _hLat hR
  exact hdim _ (le_finrank_of_shareRd (recPJ h j hj) ka _ Tn del (by omega) hR)

end GlobalTheory.RunJoin
