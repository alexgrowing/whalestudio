import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem cont_pt {K : Type} [Field K] [NumberField K] : Continuous (pt (K := K)) := by
  obtain ⟨-, -, -, hc, -⟩ := blkLaws (K := K)
  have hL : Continuous fun p : Par K => lv p.1 p.2.1 p.2.2.1 := by
    have : Continuous fun p : Par K => (p.1, p.2.1, p.2.2.1) := by fun_prop
    simpa only [Function.comp_def] using hc.comp this
  have hN : Continuous fun p : Par K => (nn p.2.2.2.2 : G1 K (2 + 2)) := (continuous_unipOne 2).comp (by fun_prop)
  exact (hN.mul hL).mul (continuous_subtype_val.comp (by fun_prop))

set_option synthInstance.maxHeartbeats 200000 in
private theorem meas_pt {K : Type} [Field K] [NumberField K] : Measurable (pt (K := K)) := by
  haveI : BorelSpace (KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : BorelSpace (ℝ × KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : SecondCountableTopology (G1 K 2) := inferInstance
  haveI : BorelSpace (G1 K 2 × ℝ × KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : BorelSpace (Par K) := Prod.borelSpace
  exact cont_pt.measurable

private theorem core {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ) (hU : Unf μ μ₂ κ c)
    (F : G1 K (2 + 2) → ℂ) (hF : Continuous F) (hP : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (hB : InBand F) (hD : Decays F)
    (v w : L2 μ) (hv : Reps μ v (th F)) (W : G1 K (2 + 2) → ℂ) (hW : Measurable W)
    (hWi : ∀ γ ∈ Gam K (2 + 2), ∀ g, W (γ * g) = W g) (hw : Reps μ w W) :
    Integrable (fun p => conj (F (pt p)) * W (pt p)) (parM μ₂ κ) ∧
      ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * W (pt p) ∂parM μ₂ κ := by
  obtain ⟨hfin, -, -, h4⟩ := thBasic μ F hF hP hB
  obtain ⟨⟨C, hC, hCb⟩, -, -⟩ := h4 hD
  have hm : Measurable fun g => conj (F g) * W g := (Complex.continuous_conj.comp hF).measurable.mul hW
  have hinv : ∀ γ ∈ PK K, ∀ g, conj (F (γ * g)) * W (γ * g) = conj (F g) * W g := fun γ hγ g => by
    obtain ⟨δ, -, rfl⟩ := id hγ
    rw [hP _ hγ]
    exact congrArg _ (hWi _ δ.2 g)
  have hwae : ∀ᵐ y ∂fd μ, (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = W y := ae_restrict_of_ae hw
  have hvae : ∀ᵐ y ∂fd μ, (v : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = th F y := ae_restrict_of_ae hv
  have hW1 : ∫⁻ y, ‖W y‖ₑ ∂fd μ < ⊤ := by
    haveI := isFiniteMeasure_quotientMeasure μ
    have h1 := ((Lp.memLp w).integrable one_le_two).2
    rw [hasFiniteIntegral_iff_enorm, lintegral_quotientMeasure] at h1
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) h1
    filter_upwards [hwae] with y hy
    rw [hy]
  have hint : Integrable (fun p => conj (F (pt p)) * W (pt p)) (parM μ₂ κ) := by
    refine ⟨(hm.comp meas_pt).aestronglyMeasurable, ?_⟩
    have h1 := hU.2.1 (fun g => ‖conj (F g) * W g‖ₑ) hm.enorm fun γ hγ g => by rw [hinv γ hγ]
    have h2 : ∫⁻ y, ∑' q : Cos K, ‖conj (F ((q.out : G1 K (2 + 2)) * y)) * W ((q.out : G1 K (2 + 2)) * y)‖ₑ ∂fd μ ≤
        ∫⁻ y, C * ‖W y‖ₑ ∂fd μ := by
      refine lintegral_mono fun y => ?_
      simp only [enorm_mul, hWi _ (Quotient.out _ : Gam K (2 + 2)).2, RCLike.enorm_conj]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (hCb y) _
    rw [lintegral_const_mul' _ _ hC, h1] at h2
    have h3 := h2.trans_lt (ENNReal.mul_lt_top hC.lt_top hW1)
    rw [hasFiniteIntegral_iff_enorm]
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (by simpa using hU.1)] at h3
    exact lt_irrefl _ h3
  refine ⟨hint, ?_⟩
  rw [← hU.2.2 _ hm hinv hint, L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [hwae, hvae] with y h1 h2
  have hf : (Function.support fun q : Cos K => F ((q.out : G1 K (2 + 2)) * y)).Finite :=
    (hfin {y} isCompact_singleton).subset fun q hq => ⟨y, rfl, hq⟩
  simp only [hWi _ (Quotient.out _ : Gam K (2 + 2)).2]
  rw [tsum_mul_right, ← Complex.conj_tsum, tsum_eq_finsum hf, h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.master :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ), Unf μ μ₂ κ c → ∀ (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F → Decays F → ∀ v w : L2 μ, Reps μ v (th F) →
      Integrable (fun p => conj (F (pt p)) * (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) (pt p))) (parM μ₂ κ) ∧
      ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) (pt p)) ∂parM μ₂ κ ∧
      ∀ Φ : G1 K (2 + 2) → ℂ, Continuous Φ → (∀ γ ∈ Gam K (2 + 2), ∀ g, Φ (γ * g) = Φ g) → Reps μ w Φ →
        Integrable (fun p => conj (F (pt p)) * Φ (pt p)) (parM μ₂ κ) ∧ ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * Φ (pt p) ∂parM μ₂ κ := by
  intro K _ _ μ _ μ₂ _ κ _ c hU F hF hP hB hD v w hv
  have h := core μ μ₂ κ c hU F hF hP hB hD v w hv
    (fun g => (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) g))
    ((Lp.stronglyMeasurable w).measurable.comp (measurable_mk _)) (fun γ hγ g => by rw [mk_mul_of_mem hγ])
    (Eventually.of_forall fun _ => rfl)
  exact ⟨h.1, h.2, fun Φ hΦ hi hw => core μ μ₂ κ c hU F hF hP hB hD v w hv Φ hΦ.measurable hi hw⟩
