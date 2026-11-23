import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionBoundedLargeNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormulaStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem nm_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {x x' : (AF F ⊗[F] E)ˣ} {n n' : (AF F)ˣ} (h : IsNm σ x n) (h' : IsNm σ x' n') : IsNm σ (x * x') (n * n') := by
  unfold IsNm at *
  have e : ((n * n' : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = ((n : AF F) ⊗ₜ[F] (1 : E)) * ((n' : AF F) ⊗ₜ[F] (1 : E)) := by
    simp
  rw [e, h, h']
  simp only [Units.val_mul, map_mul]
  ring

theorem nm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (a : (AF F)ˣ) : IsNm σ (ofF a) (a * a) := by
  unfold IsNm
  have e : ((ofF a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (a : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e]
  simp [sigR]

theorem ray_sq {F : Type} [Field F] [NumberField F] {θ : ℝ →+* Ainf F} {r : ℝ → (AF F)ˣ} (hr : IsRay θ r) {ε : ℝ}
    (hε : 0 < ε) : r (ε ^ 2) = r ε * r ε := by
  apply Units.ext
  have h1 := hr ε hε
  have h2 := hr (ε ^ 2) (by positivity)
  refine Prod.ext ?_ ?_
  · change ((r (ε ^ 2) : AF F)).1 = (r ε : AF F).1 * (r ε : AF F).1
    rw [h1.1, h2.1, ← map_mul, sq]
  · change ((r (ε ^ 2) : AF F)).2 = (r ε : AF F).2 * (r ε : AF F).2
    rw [h1.2, h2.2, one_mul]

theorem md_mul {F : Type} [Field F] [NumberField F] (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md]

theorem md_pos {F : Type} [Field F] [NumberField F] (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∃ C : ℝ≥0, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → ENNReal.ofReal (md n) * Th φ A y ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨K, hK, hdec⟩ := GlobalTheory.T.idele_class_compact_ray_decomposition F E σ hcm θ hθ r hr
  obtain ⟨R, hR⟩ := GlobalTheory.T.theta_test_function_bounded_large_norm F E σ hcm J hJ d b S φ A hT
  obtain ⟨C, hC⟩ := GlobalTheory.T.rank_one_theta_integral_ray_formula hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK (max 1 R)
  refine ⟨C, fun y n hn => ?_⟩
  obtain ⟨q, k, ε, hk, hε, rfl, hm⟩ := hdec y n hn
  rw [GlobalTheory.T.theta_series_invariant_rational_units]
  by_cases h : ε ≤ max 1 R
  · rw [hm]
    exact hC k hk ε hε h
  · have h1 : 1 < ε := lt_of_le_of_lt (le_max_left _ _) (not_le.1 h)
    have h2 : R < ε := lt_of_le_of_lt (le_max_right _ _) (not_le.1 h)
    have h3 : 2 * Module.finrank ℚ F ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := F)
      omega
    have h4 : ε ≤ ε ^ (2 * Module.finrank ℚ F) := le_self_pow₀ h1.le h3
    have h5 := hR _ n hn (by rw [hm]; linarith)
    rw [GlobalTheory.T.theta_series_invariant_rational_units] at h5
    rw [h5, mul_zero]
    exact bot_le

theorem lside : PositivityTheory.Rg.Mass.Equi → LSide := by
  intro hEq F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm θ hθ r hr S φ A hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have hG := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  haveI : IsTopologicalGroup (HA (AF F) σ J) := hG.1
  haveI : LocallyCompactSpace (HA (AF F) σ J) := hG.2.1
  haveI : SecondCountableTopology (HA (AF F) σ J) := hG.2.2.1
  haveI : T2Space (HA (AF F) σ J) := hG.2.2.2.1
  haveI : BorelSpace (HA (AF F) σ J) := hG.2.2.2.2.1
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm 1 J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm 1 J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 : μ 𝓕 ≠ 0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin).1
  have hft : μ 𝓕 ≠ ⊤ := hfin.ne
  obtain ⟨C, hC⟩ := bound hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨R, hR⟩ := GlobalTheory.T.theta_test_function_bounded_large_norm F E σ hcm J hJ d b S φ A hT
  have hM := fun x => GlobalTheory.T.rank_one_siegel_weil_theta_average F E σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  have hnm : ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ) (h : HA (AF F) σ J), IsNm σ x n → IsNm σ (x * ue (AF F) σ J h⁻¹) n :=
    fun x n h hn => by simpa using nm_mul hn (GlobalTheory.T.unitary_scalar_has_norm_one F E σ hcm J hJ h⁻¹)
  have hcan : (μ 𝓕)⁻¹ * μ 𝓕 = 1 := ENNReal.inv_mul_cancel h0 hft
  refine ⟨⟨C, fun x n hn => ?_⟩, ⟨R, fun x n hn hRn => ?_⟩, fun x n hn => ?_⟩
  · rw [(hM x).1, mul_left_comm, ← lintegral_const_mul _ (hM x).2]
    calc _ ≤ (μ 𝓕)⁻¹ * ∫⁻ _ in 𝓕, (C : ℝ≥0∞) ∂μ := by
            gcongr with h
            exact hC _ n (hnm x n h hn)
      _ = C := by
            rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (C : ℝ≥0∞), ← mul_assoc, hcan, one_mul]
  · rw [(hM x).1]
    have : ∀ h : HA (AF F) σ J, Th φ A (x * ue (AF F) σ J h⁻¹) = 0 := fun h => hR _ n (hnm x n h hn) hRn
    simp [this]
  · set m := 2 * Module.finrank ℚ F with hmdef
    have hmr := (GlobalTheory.T.ray_norm_and_module_formula F hcm.1 θ hθ r hr).2
    have hmd : ∀ ε : ℝ, 0 < ε → md (n * r (ε ^ 2)) = md n * ε ^ m := fun ε hε => by
      rw [md_mul, hmr _ (by positivity), hmdef, pow_mul]
    have hne : ∀ ε : ℝ, 0 < ε → IsNm σ (x * ofF (r ε)) (n * r (ε ^ 2)) := fun ε hε => by
      rw [ray_sq hr hε]
      exact nm_mul hn (nm_ofF _)
    set f : ℝ → HA (AF F) σ J → ℝ≥0∞ := fun ε h =>
      ENNReal.ofReal (md (n * r (ε ^ 2))) * Th φ A (x * ofF (r ε) * ue (AF F) σ J h⁻¹) with hf
    have hfm : ∀ ε, Measurable (f ε) := fun ε => (hM _).2.const_mul _
    have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h, f ε h ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with ε hε h
      exact hC _ _ (hnm _ _ h (hne ε hε))
    have hpt : ∀ h, Tendsto (fun ε => f ε h) (𝓝[>] 0) (𝓝 (vol b li lam S φ A)) := fun h => by
      have hy := hnm x n h hn
      have e0 : ∀ ε, x * ofF (r ε) * ue (AF F) σ J h⁻¹ = x * ue (AF F) σ J h⁻¹ * ofF (r ε) := fun ε => by
        rw [mul_assoc, mul_comm (ofF (r ε)), ← mul_assoc]
      have hT1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Th φ A (x * ue (AF F) σ J h⁻¹ * ofF (r ε)) ≠ ⊤ := by
        filter_upwards [hbd, self_mem_nhdsWithin] with ε h1 h2 h3
        have h4 := h1 h
        simp only [hf, e0, h3] at h4
        rw [ENNReal.mul_top (by simpa using md_pos _)] at h4
        exact absurd h4 (not_le.2 ENNReal.coe_lt_top)
      have hL := GlobalTheory.T.rank_one_theta_integral_ray_limit hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT _ n hy hT1
      have hmn : ENNReal.ofReal (md n) ≠ 0 := by simpa using md_pos n
      have h2 := ENNReal.Tendsto.const_mul hL (Or.inr (ENNReal.ofReal_ne_top (r := md n)))
      rw [← mul_assoc, ENNReal.mul_inv_cancel hmn ENNReal.ofReal_ne_top, one_mul] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [hf]
      rw [e0, hmd ε hε', ENNReal.ofReal_mul (md_pos n).le]
      exact (mul_assoc _ _ _).symm
    have hlim : Tendsto (fun ε => ∫⁻ h in 𝓕, f ε h ∂μ) (𝓝[>] 0) (𝓝 (∫⁻ _ in 𝓕, vol b li lam S φ A ∂μ)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
        (Eventually.of_forall hfm) (hbd.mono fun ε h => ae_of_all _ h) ?_ (ae_of_all _ hpt)
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hft
    have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.inv_ne_top.2 h0)) (a := (μ 𝓕)⁻¹)
    rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (vol b li lam S φ A), ← mul_assoc, hcan, one_mul] at h2
    refine h2.congr fun ε => ?_
    simp only [hf]
    rw [(hM _).1, lintegral_const_mul _ (hM _).2, mul_left_comm]
    rfl

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
