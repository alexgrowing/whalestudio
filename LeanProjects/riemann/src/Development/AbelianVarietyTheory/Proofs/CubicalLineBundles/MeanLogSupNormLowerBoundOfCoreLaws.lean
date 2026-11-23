import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DataXOfModelOfGamAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoomStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerLogOmCore
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem log_two_mul_mul_le {g₁ g₂ s d L : ℝ} (h1 : 0 < g₁) (h2 : 0 < g₂) (hs : 0 < s) (hsd : s ≤ d) (hL : 0 ≤ L)
    (b1 : Real.log g₁ ≤ 9 * L + 1) (b2 : Real.log g₂ ≤ 9 * L + 1) :
    Real.log (2 * (g₁ * g₂) * s) ≤ 19 * L + 3 + Real.log d := by
  rw [Real.log_mul (by positivity) hs.ne', Real.log_mul (by norm_num) (by positivity), Real.log_mul h1.ne' h2.ne']
  have := Real.log_le_log hs hsd
  have h2' : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  linarith

theorem lamwAt_of_lawsCore : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D), (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) → ∀ (j : ℕ) (w : WeightFamilies.Wt D j) (C A : ℝ), C0 ≤ C → 2 ≤ A → Formalism.MainNotions.Gaps.EtaleWeightGaps.LAMwAt large₂ (recB h) j w C A := by
  classical
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.T.exists_constant_cmEvaluation_fits_room
  refine ⟨C0, hC0, ?_⟩
  intro D T h hG large₂ hg j w C A hC hA F hF hF0
  have hj : InR D j := by
    by_contra hj
    exact hF0 (cutR_zero T.C hj F)
  obtain ⟨hr, hpq, hf, hsd, hd1, hlogd, hwf, hsz⟩ := GlobalTheory.WtSizes.sizes D T h j hj w
  have hFC : F.1 ∈ T.C j w := cutR_le T.C j w F.2
  have hhol : rdU (T.U j T.σ₀) F.1 ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F.1).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F.1) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hF1 : F.1 ≠ 0 := fun h0 => hF0 (Subtype.ext h0)
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F.1) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F.1)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F.1 hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
    (rdU (T.U j T.σ₀) F.1) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F.1 k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F.1 k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F.1 k) z0 := by
    linarith
  obtain ⟨Xx, hX, hXg, hΛ⟩ := GlobalTheory.LatticeData.dataXOfModel_of_gamAt D T hG j h hj T.σ₀ T.good_σ₀ k
  obtain ⟨hMk, htr⟩ := GlobalTheory.TransvModel.transv_model D T h j hj k Xx hX hXg hΛ
  have g0 := (D.host.g_prime 0).pos
  have g1 := (D.host.g_prime 1).pos
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hM : (0 : ℝ) < ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos g0 g1) hN) hdpos
  generalize ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) = M at hMk htr hM
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM
    (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by
      obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
      exact ⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz
  have hL : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hlog : Real.log (M * Xx.k0) ≤ 19 * large₂.sc.L + 3 + Real.log (dE D.host.E) := by
    rw [hMk, Nat.cast_mul]
    exact log_two_mul_mul_le (by exact_mod_cast g0) (by exact_mod_cast g1)
      (Real.sqrt_pos.2 (by exact_mod_cast hdpos)) hsd hL (hg 0) (hg 1)
  obtain ⟨hLa1, hr'⟩ := hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) large₂.sc.L large₂.logOm M Xx.k0 w.size hf1 hr
    Xx.p0_le hd1 hL hM Xx.minWeight_pos w.one_le_size hlog
  have hr'' := hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C A hC hA
  obtain ⟨_, χ, hχ, hOm⟩ := GlobalTheory.LamT.exists_kronecker_logOm_core D T h large₂
  have hsup : ∀ σ, (recB h).supN j w σ F =
      supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F.1 := fun σ => by
    change cutN T.C T.Ns j w σ F = _
    unfold cutN Core.Ns
    rw [if_pos hj]
  have hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F.1 := fun σ => by
    rw [← hsup]
    exact lt_of_le_of_ne ((recB h).supN_nonneg j w σ F) fun h0 => hF0 (((recB h).supN_eq_zero j w σ F).1 h0.symm)
  have h5 := GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (h.unf j hj)
    (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F.1 hFC hF hSpos k ⟨x, hx⟩ Xx hX D.host.AA
    (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  have h3 : WeightFamilies.meanLogSup (recB h) F =
      (∑ σ : T.Q.c.F →+* ℂ, Real.log (supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F.1)) /
      (Module.finrank ℚ T.Q.c.F : ℝ) := by
    rw [WeightFamilies.meanLogSup, NumberField.Embeddings.card T.Q.c.F ℂ]
    exact congrArg (· / _) (Finset.sum_congr rfl fun σ _ => congrArg Real.log (hsup σ))
  rw [h3]
  refine le_trans ?_ h5
  have hf' : Module.finrank ℚ D.host.E / 2 = D.R.f := hf
  rw [hOm, hf']
  have hP : WeightFamilies.PP0v D large₂ C A = C * ((fdeg D.host.E : ℝ) * D.R.r + large₂.sc.L + Real.log (dE D.host.E) + |large₂.logOm|) ^ A := by
    rw [WeightFamilies.PP0v, hf, hlogd]
  rw [hP]
  linarith

end GlobalTheory
