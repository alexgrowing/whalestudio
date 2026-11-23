import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBoundedStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLatticeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBoundsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFiniteSpanningShortGeneratorsSmallSupNormStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLatticeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem scalB_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  intro hCI D T h hGam hSh hA hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hHP hRows hSpF hSpF0 hSpK
  obtain ⟨-, hSet, -, -, -⟩ := id hHP
  obtain ⟨hkaN, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hIsL, hIsF, -, -, -, -, -, h40, -, -, -, -⟩ := hSet
  have hLn : wL.n = nW := hIsL.1
  have hkn : ka.n = nP + Tn * nW := hkaN.trans hnV
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    · exact D.host.pde_prime.pos
    · exact D.host.pde'_prime.pos
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hHP
  have hsz := GlobalTheory.T.runScalars_ne_zero_and_log_bounded D (recB h.toLawsCore) hinj EX j p ka wL wF Tn nP nW hp0 (by omega) hLn hIsF hkn
  have hsW := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hWeq := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)

  have hW : ∀ w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w ∧ D.R.r ≤ w.n ∧ w.LastPos := by
    intro w hw
    obtain ⟨hdf, hn, hr, hlast⟩ := hwb.1 w hw
    exact ⟨GlobalTheory.pageRows_of_le D large₂ j ka w (by linarith) hdf hn hRows, hr, hlast⟩

  have hShort : ∀ (w : WeightFamilies.Wt D j) (s : 𝓞 (recB h.toLawsCore).KO) (c : ℝ),
      w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → s ≠ 0 → 0 ≤ c →
      c ≤ 2 * (lamStar D + 2 * Real.log p) * w.size →
      (∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ (s : (recB h.toLawsCore).KO)‖ ≤ c) →
      ShortG (recPJ h j hj) w ((recPJ h j hj).Thc s w) (Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) p * w.size) := by
    intro w s c hw hsp hs hc0 hc hsc
    obtain ⟨hRw, hrw, hlw⟩ := hW w hw
    have hn8 : 0 < w.n := by omega
    obtain ⟨Sh, hSh1, hSh2⟩ := GlobalTheory.T.exists_finite_spanning_short_generators_small_supNorm hCI D T h hGam large₂ j hj w hRw hL2 hrw hlw hSh (hA j hj w.n) hsp
    have hsize : 1 ≤ w.size := WeightFamilies.Wt.one_le_size w
    have key := GlobalTheory.T.shortGenerators_scaled_thetaLattice D _ _ j (recPJ h j hj) w s Sh c (400 * Zb D large₂ * w.size) hs hc0
      (mul_nonneg (by linarith) (by linarith)) hsc hSh1 hSh2
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w p hL2 hn8).2.1
    unfold ShortG at key ⊢
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := key
    exact ⟨S', hS'1, hS'2, fun g hg => (hS'3 g hg).trans (by nlinarith)⟩
  unfold ScalB
  refine ⟨hWeq ▸ hsW.1, hsz.1, hsz.2.1, hsz.2.2.1, fun σ => ?_, p, (Formalism.MainNotions.Gaps.FamilyHypotheses.ownPr_iff D p).1 hp,
    fun σ => hsz.2.2.2 σ, 1009 * Zb D large₂, le_rfl, ?_⟩
  · rw [hWeq]
    exact ⟨(hsW.2 σ).1, (hsW.2 σ).2.1⟩
  unfold S4
  have hsizeL : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hRL, hrL, hlL⟩ := hW wL (by simp)
    have hnL : 0 < wL.n := by omega
    obtain ⟨N, w0, hspan, -, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hCI D T h hGam large₂ j hj wL hRL hL2 hrL hlL
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL p hL2 hnL).2.2
    have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
      rw [Real.log_abs]
      exact Real.log_intCast_nonneg _
    have hb : 0 ≤ 400 * Zb D large₂ * wL.size + 3 * D.R.f * D.R.r * wL.n * large₂.sc.L +
        5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) +
        Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
      have h1 : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ (3 * D.R.f * D.R.r * wL.n : ℝ) * large₂.sc.L := mul_nonneg (by positivity) (by linarith)
      have h3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO :=
        div_nonneg hdisc (by positivity)
      have h4 : 0 ≤ 400 * Zb D large₂ * wL.size := mul_nonneg (by linarith) (by linarith)
      linarith
    exact (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF _ N w0 _ _ _ 0
      (mul_nonneg (by linarith) (by linarith)) hb (fun σ => (hsz.2.2.2 σ).1) hspan hsup hG).1
  · have hsF : ∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sF : (recB h.toLawsCore).KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size :=
      fun σ => (hsz.2.2.2 σ).2.1
    exact hShort wF _ _ (by simp) hSpF hsz.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size wF])) (by nlinarith [WeightFamilies.Wt.one_le_size wF]) hsF
  · exact hShort _ _ _ (by simp) hSpF0 hsz.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ((recPJ h j hj).wF0 wL wF)])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.1)
  · exact hShort ka _ _ (by simp) hSpK hsz.2.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ka])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.2)

end GlobalTheory.RunIn
