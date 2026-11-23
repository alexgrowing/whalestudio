import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHostStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem fg_of_trivAt_even {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

theorem sh_mem_span_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  intro hCI D T h hG large₂ j hj w hP hL hrn hlp hS hA g hg
  obtain ⟨hgs, Λ, N, x0, P, hU, hT1, hT2, hLev, hAdm, hPh, hR⟩ := hg
  obtain ⟨-, -, -, -, -, hfd, -, hrd, hfr, hf1, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hP.2.1 hP.2.2.1 hP.2.2.2.1
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := ((GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).1
  have hfg : Λ.La.FG := fg_of_trivAt_even Λ (by
    unfold badN
    have h2 : 2 ∣ D.host.QS := (D.host.mem_small_iff.1 D.host.two_mem_small).2
    exact ((h2.mul_right _).mul_right _).mul_right _) hT1
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have e : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = absA w := by
    unfold absA Formalism.MainNotions.WeightAlgebra.DF degP
    push_cast
    rfl
  obtain ⟨S, hS1, hS2, -⟩ := GlobalTheory.T.exists_short_harmonic_family_unimodular D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n Λ hU hfg (hr ▸ hrn) (wtA w)
    large₂.sc.L hL hrd (by rw [hfd]; exact hP.2.2.2.2.1)
    ((Real.log_le_log (by positivity) (by linarith)).trans hP.2.2.2.2.2.2.2.1) hP.2.2.2.2.2.2.2.2
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hS2 P hPh.1)
  have hQ : ∀ i, (Q i).1 ∈ harmL T.Q.c Λ (wtA w) := fun i => (hS1 _ (Q i).2).1
  choose gs hgs1 hgs2 using fun i =>
    (hS.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x0 (Q i).1 hU hT1 hT2 hLev hAdm (hQ i)).2
  have hlin := GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial hCI D T h hS j hj w Λ N x0 hU hT2 hLev m cf (fun i => (Q i).1) g gs hQ hgs hgs1
    (by rw [hsum]; exact hR) hgs2
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨hgs1 i, Λ, N, x0, (Q i).1, hU, hT1, hT2, hLev, hAdm, hQ i, hgs2 i⟩, fun σ => ?_⟩)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hA0 : 0 ≤ absA w := by rw [← e]; positivity
  have hb : Real.log (l1At σ (Q i).1) ≤ 140 * D.R.r * large₂.sc.L * absA w := by
    refine ((hS1 _ (Q i).2).2 σ).trans ?_
    rw [hr, ← e]
    exact mul_le_mul_of_nonneg_left hdf (by positivity)
  have hl1 : l1At σ (Q i).1 ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hb)
  have hsup := GlobalTheory.T.log_supNorm_shortThetaGenerator_le hCI D T h hG large₂ j hj w hP hL hrn (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlp) hS hA
    Λ N x0 (Q i).1 (gs i) hU hT1 hT2 hLev hAdm (hQ i) (hgs2 i) (hgs1 i) σ _ (by positivity) hl1
  exact hsup.trans (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL (by omega)).1

end GlobalTheory.RunIn
