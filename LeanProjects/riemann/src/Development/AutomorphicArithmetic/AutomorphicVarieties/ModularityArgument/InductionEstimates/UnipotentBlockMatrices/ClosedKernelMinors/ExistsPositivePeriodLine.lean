import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BumpEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Heckify
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped Pointwise

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

private theorem res_zpow_neg_mul_res_zpow_neg_eq_inv_res (μ ν : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure ν] {U C : Set G} (hU : IsCompact U)
    (hC : IsCompact C) (hν : ∀ᵐ k ∂ν, k ∈ U) (F : G → G → ℂ) (hF : Continuous (Function.uncurry F))
    (h0 : ∀ k ∈ U, ∀ g, g ∉ C → F g k = 0) : ∫ g, ∫ k, F g k ∂ν ∂μ = ∫ k, ∫ g, F g k ∂μ ∂ν := by
  apply integral_integral_swap
  have h1 : IntegrableOn (Function.uncurry F) (C ×ˢ U) (μ.prod ν) :=
    hF.continuousOn.integrableOn_compact (hC.prod hU)
  refine h1.integrable_of_ae_notMem_eq_zero ?_
  have h2 : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ U := (Measure.quasiMeasurePreserving_snd).ae hν
  filter_upwards [h2] with p hp hn
  exact h0 p.2 hp p.1 fun hc => hn ⟨hc, hp⟩

private theorem cont_avg (ν : Measure G) [IsProbabilityMeasure ν] {U : Set G} (hU : IsCompact U)
    (hν : ∀ᵐ k ∂ν, k ∈ U) (F : G → G → ℂ) (hF : Continuous (Function.uncurry F)) :
    Continuous fun g => ∫ k, F g k ∂ν := by
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hU
  rwa [Measure.restrict_eq_self_of_ae_mem hν] at h

private theorem convolution_hecke_identity (μ ν : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) (e a₀ a φ : G → ℂ) (he : Continuous e) (ha₀ : Continuous a₀)
    (hc : HasCompactSupport a₀) (hφ : Continuous φ) (hfix : ∀ g, ∫ k, e k * φ (g * k) ∂ν = φ g)
    (ha : ∀ g, a g = ∫ k, ∫ k', e k * a₀ (k⁻¹ * g * k'⁻¹) * e k' ∂ν ∂ν) (x : G) :
    ∫ g, a g * φ (x * g) ∂μ = ∫ k, e k * ∫ h, a₀ h * φ (x * k * h) ∂μ ∂ν := by
  set b : G → ℂ := fun g => ∫ k', a₀ (g * k'⁻¹) * e k' ∂ν with hb
  have hbc : Continuous b := cont_avg ν hU hν (fun g k' => a₀ (g * k'⁻¹) * e k') (by
    unfold Function.uncurry; fun_prop)
  have hz : ∀ k ∈ U, ∀ g, g ∉ tsupport a₀ * U → a₀ (g * k⁻¹) = 0 := by
    intro k hk g hg
    by_contra hne
    exact hg ⟨g * k⁻¹, subset_tsupport _ hne, k, hk, by simp⟩
  have hb0 : ∀ g, g ∉ tsupport a₀ * U → b g = 0 := by
    intro g hg
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hν] with k hk
    simp [hz k hk g hg]
  have hC : IsCompact (tsupport a₀ * U) := IsCompact.mul hc hU
  have h1 : ∀ y, ∫ g, b g * φ (y * g) ∂μ = ∫ h, a₀ h * φ (y * h) ∂μ := by
    intro y
    have s1 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU hC hν (fun g k => a₀ (g * k⁻¹) * e k * φ (y * g))
      (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by simp [hz k hk g hg])
    have s2 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU hc hν (fun g k => a₀ g * (e k * φ (y * g * k)))
      (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by simp [image_eq_zero_of_notMem_tsupport hg])
    simp only [integral_mul_const, integral_const_mul, hfix] at s1 s2
    rw [s1, s2]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [← integral_mul_right_eq_self (fun g => a₀ (g * k⁻¹) * e k * φ (y * g)) k]
    simp [mul_assoc]
  have s3 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU (hU.mul hC) hν (fun g k => e k * (b (k⁻¹ * g) * φ (x * g)))
    (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by
      have : k⁻¹ * g ∉ tsupport a₀ * U := fun h => hg ⟨k, hk, _, h, by simp⟩
      simp [hb0 _ this])
  have h2 : ∀ g, a g * φ (x * g) = ∫ k, e k * (b (k⁻¹ * g) * φ (x * g)) ∂ν := by
    intro g
    rw [ha, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [hb, mul_assoc (e k), integral_const_mul]
  simp only [h2]
  rw [s3]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [integral_const_mul]
  rw [← h1, ← integral_mul_left_eq_self (fun g => b (k⁻¹ * g) * φ (x * g)) k]
  simp [mul_assoc]

private theorem convolution_estimate (μ ν : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) (e a₀ φ : G → ℂ) (he : Continuous e) (ha₀ : Continuous a₀)
    (hc : HasCompactSupport a₀) (hφ : Continuous φ) (hfix : ∀ g, ∫ k, e k * φ (g * k) ∂ν = φ g)
    (hpos : ∀ g, 0 ≤ (a₀ g).re ∧ (a₀ g).im = 0) (hone : ∫ g, a₀ g ∂μ = 1) (x : G) (ε : ℝ)
    (hε : ∀ k ∈ U, ∀ h ∈ tsupport a₀, ‖e k‖ * ‖φ (x * k * h) - φ (x * k)‖ ≤ ε) (hε0 : 0 ≤ ε) :
    ‖(∫ k, e k * ∫ h, a₀ h * φ (x * k * h) ∂μ ∂ν) - φ x‖ ≤ ε := by
  have hI : Continuous fun k => ∫ h, a₀ h * φ (x * k * h) ∂μ := by
    have h := continuous_parametric_integral_of_continuous (μ := μ) (f := fun k h => a₀ h * φ (x * k * h))
      (by unfold Function.uncurry; fun_prop) hc
    refine h.congr fun k => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by simp [image_eq_zero_of_notMem_tsupport hh]
  have hint : ∀ F : G → ℂ, Continuous F → Integrable F ν := fun F hF => by
    have := hF.continuousOn.integrableOn_compact (μ := ν) hU
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at this
  have hai : Integrable a₀ μ := ha₀.integrable_of_hasCompactSupport hc
  have hn : ∫ g, ‖a₀ g‖ ∂μ = 1 := by
    have : ∀ g, ‖a₀ g‖ = RCLike.re (a₀ g) := fun g => by
      have h2 : a₀ g = ((a₀ g).re : ℂ) := Complex.ext (by simp) (by simp [(hpos g).2])
      rw [RCLike.re_to_complex, h2, Complex.norm_real, Real.norm_of_nonneg (hpos g).1, Complex.ofReal_re]
    simp only [this]
    rw [integral_re hai, hone]
    simp
  rw [← hfix x, ← integral_sub (hint (fun k => e k * ∫ h, a₀ h * φ (x * k * h) ∂μ) (he.mul hI))
    (hint (fun k => e k * φ (x * k)) (by fun_prop))]
  have hb : ∀ᵐ k ∂ν, ‖e k * (∫ h, a₀ h * φ (x * k * h) ∂μ) - e k * φ (x * k)‖ ≤ ε := by
    filter_upwards [hν] with k hk
    have i1 : Integrable (fun h => a₀ h * φ (x * k * h)) μ :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop) hc.mul_right
    have e1 : e k * (∫ h, a₀ h * φ (x * k * h) ∂μ) - e k * φ (x * k) =
        ∫ h, e k * (a₀ h * φ (x * k * h) - a₀ h * φ (x * k)) ∂μ := by
      rw [integral_const_mul, integral_sub i1 (hai.mul_const _), integral_mul_const, hone]
      ring
    rw [e1]
    refine (norm_integral_le_of_norm_le (hai.norm.mul_const ε) (Eventually.of_forall fun h => ?_)).trans ?_
    · by_cases hh : h ∈ tsupport a₀
      · rw [← mul_sub, norm_mul, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hε k hk h hh) (norm_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hh]
    · rw [integral_mul_const, hn, one_mul]
  simpa using norm_integral_le_of_norm_le_const hb

omit [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem exists_uniform_neighborhood {d : ℕ} (S : Eu d →ₗ[ℂ] (G → ℂ)) (hinj : Function.Injective S) (hS : ∀ v, Continuous (S v))
    (H e : G → ℂ) (hH : Continuous H) (hH0 : ∀ g, H g ≠ 0) (he : Continuous e) {U : Set G} (hU : IsCompact U) :
    ∃ O ∈ 𝓝 (1 : G), ∀ v ∈ Metric.sphere (0 : Eu d) 1, ∃ x, ∃ ε, 0 ≤ ε ∧ ε < ‖H x * S v x‖ ∧ ∀ k ∈ U, ∀ h ∈ O,
      ‖e k‖ * ‖H (x * k * h) * S v (x * k * h) - H (x * k) * S v (x * k)‖ ≤ ε := by
  have hj : Continuous fun p : Eu d × G => S p.1 p.2 := by
    have : (fun p : Eu d × G => S p.1 p.2) = fun p => ∑ i, p.1 i * S (EuclideanSpace.single i 1) p.2 := by
      funext p
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr p.1]
      simp
    rw [this]
    refine continuous_finset_sum _ fun i _ => Continuous.mul (by fun_prop) ((hS _).comp continuous_snd)
  refine (isCompact_sphere (0 : Eu d) 1).induction_on (p := fun s => ∃ O ∈ 𝓝 (1 : G), ∀ v ∈ s, ∃ x, ∃ ε, 0 ≤ ε ∧
    ε < ‖H x * S v x‖ ∧ ∀ k ∈ U, ∀ h ∈ O,
      ‖e k‖ * ‖H (x * k * h) * S v (x * k * h) - H (x * k) * S v (x * k)‖ ≤ ε) ⟨univ, univ_mem, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨O, hO, h⟩
    exact ⟨O, hO, fun v hv => h v (hst hv)⟩
  · rintro s t ⟨O, hO, h⟩ ⟨O', hO', h'⟩
    refine ⟨O ∩ O', inter_mem hO hO', ?_⟩
    rintro v (hv | hv)
    · obtain ⟨x, ε, h1, h2, h3⟩ := h v hv
      exact ⟨x, ε, h1, h2, fun k hk g hg => h3 k hk g hg.1⟩
    · obtain ⟨x, ε, h1, h2, h3⟩ := h' v hv
      exact ⟨x, ε, h1, h2, fun k hk g hg => h3 k hk g hg.2⟩
  · intro v₀ hv₀
    have hne : S v₀ ≠ 0 := by
      intro h
      have : v₀ = 0 := hinj (by rw [h, map_zero])
      simp [this] at hv₀
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    have hp : 0 < ‖H x * S v₀ x‖ := norm_pos_iff.2 (mul_ne_zero (hH0 x) hx)
    set ε := ‖H x * S v₀ x‖ / 2 with hε
    have c1 : Continuous fun z : (Eu d × G) × G =>
        ‖e z.2‖ * ‖H (x * z.2 * z.1.2) * S z.1.1 (x * z.2 * z.1.2) - H (x * z.2) * S z.1.1 (x * z.2)‖ := by
      have j1 : Continuous fun z : (Eu d × G) × G => S z.1.1 (x * z.2 * z.1.2) :=
        hj.comp (f := fun z : (Eu d × G) × G => (z.1.1, x * z.2 * z.1.2)) (by fun_prop)
      have j2 : Continuous fun z : (Eu d × G) × G => S z.1.1 (x * z.2) :=
        hj.comp (f := fun z : (Eu d × G) × G => (z.1.1, x * z.2)) (by fun_prop)
      exact (he.comp continuous_snd).norm.mul
        (((hH.comp (by fun_prop)).mul j1).sub ((hH.comp (by fun_prop)).mul j2)).norm
    have e1 : ∀ᶠ p : Eu d × G in 𝓝 (v₀, 1), ∀ k ∈ U,
        ‖e k‖ * ‖H (x * k * p.2) * S p.1 (x * k * p.2) - H (x * k) * S p.1 (x * k)‖ < ε := by
      refine hU.eventually_forall_of_forall_eventually fun k _ => ?_
      exact c1.continuousAt.eventually_lt continuousAt_const (by
        simp only [mul_one, sub_self, norm_zero, mul_zero]; exact half_pos hp)
    have c2 : Continuous fun v : Eu d => ‖H x * S v x‖ :=
      (continuous_const.mul (hj.comp (f := fun v : Eu d => (v, x)) (by fun_prop))).norm
    have e2 : ∀ᶠ v in 𝓝 v₀, ε < ‖H x * S v x‖ :=
      continuousAt_const.eventually_lt c2.continuousAt (half_lt_self hp)
    rw [nhds_prod_eq, eventually_prod_iff] at e1
    obtain ⟨pa, hpa, pb, hpb, h⟩ := e1
    refine ⟨{v | pa v ∧ ε < ‖H x * S v x‖}, mem_nhdsWithin_of_mem_nhds (hpa.and e2), {g | pb g}, hpb, ?_⟩
    intro v hv
    exact ⟨x, ε, (half_pos hp).le, hv.2, fun k hk g hg => (h hv.1 hg k hk).le⟩

end SlopeTestRemainingChoices

private theorem exists_positive_period_line {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d) :
    ∃ O ∈ 𝓝 (1 : G1 K (2 + 2)), ∀ a₀ a : CC K (2 + 2), tsupport a₀ ⊆ O → (∀ g, 0 ≤ (a₀ g).re ∧ (a₀ g).im = 0) →
      ∫ g, a₀ g ∂μ = 1 → (∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν) →
      ∀ T : Eu d →L[ℂ] Eu d, (∀ v x, ∫ g, a g * flat 0 (A.sec v) (x * g) ∂μ = flat 0 (A.sec (T v)) x) → IsUnit T := by
  obtain ⟨hU, hle, -⟩ := typeFin D
  obtain ⟨-, hk, -, hc, -⟩ := hpSpec (K := K)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hc))
  obtain ⟨O, hO, h⟩ := exists_uniform_neighborhood A.sec A.inj (fun v => (hsec v).1.cont) _ D.e hH (fun _ => Complex.exp_ne_zero _) D.cont hU
  refine ⟨O, hO, fun a₀ a hs hpos hone ha T hT => ?_⟩
  haveI := D.prob
  haveI := isMulRightInvariant_normOneGL μ
  have key : ∀ v ∈ Metric.sphere (0 : Eu d) 1, T v ≠ 0 := by
    intro v hv h0
    obtain ⟨x, ε, h1, h2, h3⟩ := h v hv
    have hφ : Continuous (flat 0 (A.sec v)) := hH.mul (hsec v).1.cont
    have hfix : ∀ g, ∫ k, D.e k * flat 0 (A.sec v) (g * k) ∂D.ν = flat 0 (A.sec v) g := by
      intro g
      unfold flat
      rw [← (hsec v).2 g, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [D.supp] with k hk'
      rw [show HP 2 2 (g * k) = HP 2 2 g from (hk k (hle hk')).2 g]
      ring
    have e1 := convolution_hecke_identity μ D.ν hU D.supp D.e a₀ a _ D.cont a₀.continuous a₀.hasCompactSupport hφ hfix ha x
    have e2 := convolution_estimate μ D.ν hU D.supp D.e a₀ _ D.cont a₀.continuous a₀.hasCompactSupport hφ hfix hpos hone x ε
      (fun k hk g hg => h3 k hk g (hs hg)) h1
    rw [← e1, hT, h0, map_zero] at e2
    have e3 : flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := by simp [flat]
    rw [e3, zero_sub, norm_neg] at e2
    exact absurd e2 (not_le.2 h2)
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hne
    refine key (((‖v‖⁻¹ : ℝ) : ℂ) • v) ?_ (by rw [map_smul, hv, smul_zero])
    simp [norm_smul, hn]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (T : Eu d →ₗ[ℂ] Eu d))).1 hinj⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.unitB :
    UnitB := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨O, hO, h⟩ := exists_positive_period_line μ A
  obtain ⟨O', hO', h'⟩ := exists_positive_period_line μ A'
  obtain ⟨a₀, hs, hpos, hone, hst, hsm⟩ := bumpEx μ (O ∩ O') (inter_mem hO hO')
  obtain ⟨a, hH, hst', hsm', ha⟩ := heckify μ D a₀ hst hsm
  obtain ⟨β, hβ⟩ := convR K μ μ₂ τ₁ τ₂ hP D d d' A A' a hH
  obtain ⟨β', hβ'⟩ := convR K μ μ₂ τ₂ τ₁ ⟨hP.irr₂, hP.irr₁, hP.orth.symm⟩ D d' d A' A a hH
  exact ⟨a, β, β', hsm', hH, hst', hβ, hβ',
    h a₀ a (hs.trans inter_subset_left) hpos hone ha _ (hβ.2.2 0),
    h' a₀ a (hs.trans inter_subset_right) hpos hone ha _ (hβ'.2.2 0)⟩
