import CompanionTheory.AutomorphicTheory.ThetaDilations.OrbitAdelic
import CompanionTheory.AutomorphicTheory.ThetaDilations.ProdRho
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomainStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionCuspExpansionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

set_option maxHeartbeats 400000 in
theorem bounded : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → wt M τ * ‖((∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ)‖ ≤ C := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM Ω _ Pr gf gi hC φ hφ
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hO := hC.2.2.2.1
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ, ∀ φ τ,
    𝒟 φ τ = (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ := ⟨_, fun _ _ => rfl⟩
  have hUD := fun ω => GlobalTheory.T.theta_function_modularity F ψ hψ ι M B ρ P hQ _ _ (hO ω)
  have hei := GlobalTheory.T.theta_function_cusp_expansion F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have heb := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have hti := GlobalTheory.T.theta_average_integral_formula F lf hlf h1 ψ hψ ι M B ρ P hQ Ω Pr gf gi hC
  have hsm : ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ := fun φ τ hφ hτ c => by
    simp only [h𝒟, fun ω => (hUD ω φ τ).2.2 c, (hei φ hφ τ hτ).2.2.2 c, integral_const_mul, mul_sub]
  have good := good_ex hlf h1 hψ hQ (𝒟 := 𝒟) fun φ τ hφ hτ =>
    ⟨fun b => by simp only [h𝒟, fun ω => (hUD ω φ τ).1 b, (hei φ hφ τ hτ).1 b],
      fun a ha => by simp only [h𝒟, fun ω => (hUD ω φ τ).2.1 a ha, (hei φ hφ τ hτ).2.1 a ha],
      by simp only [h𝒟, mul_sub, ← integral_const_mul, (hei φ hφ τ hτ).2.2.1,
        fun ω => GlobalTheory.T.theta_function_automorphy F lf hlf h1 ψ hψ ι M B ρ P hQ _ _ (hO ω) φ hφ τ hτ], hsm φ τ hφ hτ⟩
  have hadd : ∀ τ, (∀ w, 0 < (τ w).im) → ∀ φ φ', SB φ → SB φ' → 𝒟 (φ + φ') τ = 𝒟 φ τ + 𝒟 φ' τ := by
    intro τ hτ φ φ' hφ hφ'
    obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => (τ w).im
    have e1 : ∀ ω, theta B ρ P (gf ω) (gi ω) (φ + φ') τ =
        theta B ρ P (gf ω) (gi ω) φ τ + theta B ρ P (gf ω) (gi ω) φ' τ := fun ω => by
      have hs := (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ _ _ (hO ω) τ hτ).1
      rw [theta, theta, theta, ← (hs φ hφ).of_norm.tsum_add (hs φ' hφ').of_norm]
      simp only [thTerm, Pi.add_apply, add_mul]
    have e2 : ∀ b, eiTerm ψ lf B ρ P (φ + φ') τ b = eiTerm ψ lf B ρ P φ τ b + eiTerm ψ lf B ρ P φ' τ b := fun b => by
      rw [eiTerm, eiTerm, eiTerm, ← add_mul, fstar, fstar, fstar,
        ← integral_add (sb_int H.2.2.2.2.2 (sb_opU H _ hφ)) (sb_int H.2.2.2.2.2 (sb_opU H _ hφ'))]
      simp only [opU, Pi.add_apply, mul_add]
    obtain ⟨_, s1⟩ := heb φ hφ _ (hτ w₀)
    obtain ⟨_, s2⟩ := heb φ' hφ' _ (hτ w₀)
    simp only [h𝒟, e1, eis, e2, Pi.add_apply, integral_add (hti φ τ hφ hτ).1 (hti φ' τ hφ' hτ).1,
      (s1 τ hw₀).1.of_norm.tsum_add (s2 τ hw₀).1.of_norm]
    ring
  obtain ⟨S, κ, t, hκ, ht, hred⟩ := GlobalTheory.T.reduction_to_siegel_domain F hQ.1 ρ hQ.2.2.2.2.1
  have hwt : ∀ τ : InfinitePlace F → ℂ, 0 ≤ wt M τ := fun τ => Finset.prod_nonneg fun _ _ => by positivity
  have hS : ∀ φ, SB φ → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      (∀ v w, κ * (τ w).im ≤ (τ v).im) → wt M τ * ‖𝒟 φ τ‖ ≤ C := fun φ hφ => by
    obtain ⟨C₁, b1⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ κ t hκ ht
    obtain ⟨C₂, b2⟩ := heb φ hφ t ht
    refine ⟨|C₁| + |C₂|, by positivity, fun τ h2 h3 => ?_⟩
    have hτ : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (h2 w)
    have h4 := (mul_le_mul_right (hti φ τ hφ hτ).2 _).trans (b1 τ h2 h3).2
    rw [← ENNReal.ofReal_mul (hwt τ)] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg C₁)).1 (h4.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
    have h6 : ‖𝒟 φ τ‖ ≤ ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ + ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ := by
      simp only [h𝒟, eis, ← sub_sub]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm (b2 τ h2).1))
    refine (mul_le_mul_of_nonneg_left h6 (hwt τ)).trans ?_
    rw [mul_add]
    exact add_le_add h5 ((b2 τ h2).2.trans (le_abs_self _))
  choose T hT1 hT2 using good
  obtain ⟨L, s, C₀, hL, horb⟩ := orbit_adelic H hφ
  have := H.2.2.2.2.2.1
  have := H.2.2.2.2.2.2.1
  choose C hC0 hCb using fun (r : SL(2, F)) (a : ι → A F) => hS _ ((hT1 r).1 _ (sb_ind a hL))
  refine ⟨∑ r ∈ S, ∑ a ∈ s, |C₀| * C r a, fun τ hτ => ?_⟩
  rw [← h𝒟]
  obtain ⟨r, hr, k, hk, h2, h3⟩ := hred τ hτ
  have hmob := GlobalTheory.T.mobius_action_upper_half_plane F ρ τ hτ
  obtain ⟨-, c, hc, e⟩ := horb (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) k) (fun i j => ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 (k i j)).2 (hk i j)) _ (hT1 k)
  have hτ' : ∀ w, 0 < (mob ρ (r * k) τ w).im := fun w => (hmob.1 _ w).2
  rw [← hT2 k φ τ hφ hτ, ← hT2 r _ _ ((hT1 k).1 φ hφ) fun w => (hmob.1 k w).2, ← hmob.2.1, e,
    map_sum_sb (hT1 r).2.2.1 (hT1 r).2.2.2.1 s c fun a => sb_ind a hL]
  have e2 := congrFun (map_sum_sb (T := fun φ _ => 𝒟 φ (mob ρ (r * k) τ))
    (fun φ φ' h h' => funext fun _ => hadd _ hτ' φ φ' h h') (fun c φ h => funext fun _ => hsm φ _ h hτ' c) s c
    fun a => (hT1 r).1 _ (sb_ind a hL)) 0
  rw [e2, Finset.sum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ a ∈ s, |C₀| * C r a)
    (fun r _ => Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (hC0 r a)) hr)
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hwt _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_left_comm]
  exact mul_le_mul ((hc a).trans (le_abs_self _)) (hCb r a _ h2 h3) (mul_nonneg (hwt _) (norm_nonneg _)) (abs_nonneg _)

end CompanionTheory.PlacePermOperatorBicommutantSpan
