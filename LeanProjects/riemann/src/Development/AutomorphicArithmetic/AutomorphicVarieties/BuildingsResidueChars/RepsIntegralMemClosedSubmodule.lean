import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem inner_eq_setIntegral_of_ae (w v : Lp ℂ 2 (quotientMeasure Γ μ)) {g : G → ℂ}
    (h : ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = g y) :
    inner ℂ w v = ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * g y ∂μ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

private theorem closed_stable [IsFiniteMeasure (quotientMeasure Γ μ)]
    (τ : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))) (hτ : IsClosed (τ : Set (Lp ℂ 2 (quotientMeasure Γ μ))))
    (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G → ℂ)
    (hc : Continuous (fun p : U × G => Ψ p.1 p.2)) (hb : ∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C)
    (hinv : ∀ u, ∀ γ ∈ Γ, ∀ m, Ψ u (γ * m) = Ψ u m)
    (hrep : ∀ u, ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = Ψ u y) :
    ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = ∫ u, Ψ u y ∂lam := by
  obtain ⟨C, hC⟩ := hb
  choose v hvτ hvr using hrep
  let Φ : G → ℂ := fun m => ∫ u, Ψ u m ∂lam
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
    · intro m
      exact (hc.comp (by fun_prop : Continuous fun u : U => (u, m))).aestronglyMeasurable
    · intro m
      exact Eventually.of_forall fun u => hC u m
    · exact Eventually.of_forall fun u => hc.comp (by fun_prop : Continuous fun m => (u, m))
  have hΦb : ∀ m, ‖Φ m‖ ≤ C * lam.real univ := fun m =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => hC u m)
  let f : RightCosetSpace Γ → ℂ := Quotient.lift Φ (by
    rintro a b ⟨γ, rfl⟩
    change Φ ((γ : G) * b) = Φ b
    simp only [Φ, hinv _ _ γ.2])
  have hfc : Continuous f :=
    (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 hΦc
  have hf2 : MemLp f 2 (quotientMeasure Γ μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable (C * lam.real univ) (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ q
      exact hΦb y)
  have hrepΦ : ∀ᵐ y ∂μ, ((hf2.toLp f : Lp ℂ 2 (quotientMeasure Γ μ)) : RightCosetSpace Γ → ℂ) (mk Γ y) = Φ y := by
    have h := (quasiMeasurePreserving_mk Γ μ).ae (MemLp.coeFn_toLp hf2)
    filter_upwards [h] with y hy
    rw [hy]
    rfl
  refine ⟨hf2.toLp f, ?_, hrepΦ⟩
  haveI : CompleteSpace τ := hτ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]
  intro w hw
  rw [inner_eq_setIntegral_of_ae Γ μ w _ hrepΦ]
  have hw1 : Integrable (fun y => w (mk Γ y)) (μ.restrict (fundamentalDomain Γ)) := by
    have h1 : Integrable w (quotientMeasure Γ μ) :=
      (Lp.memLp w).integrable (by norm_num)
    exact Integrable.comp_measurable h1 (measurable_mk Γ)
  have hwm : StronglyMeasurable (fun y => w (mk Γ y)) := stronglyMeasurable_lift Γ μ w
  have hint : Integrable (Function.uncurry fun (u : U) (y : G) =>
      conj (w (mk Γ y)) * Ψ u y) (lam.prod (μ.restrict (fundamentalDomain Γ))) := by
    refine Integrable.mono' ((hw1.norm.mul_const C).comp_snd lam) ?_ ?_
    · have h1 : StronglyMeasurable (fun p : U × G => conj (w (mk Γ p.2))) :=
        continuous_star.comp_stronglyMeasurable (hwm.comp_measurable measurable_snd)
      exact h1.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC p.1 p.2) (norm_nonneg _)
  calc ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Φ y ∂μ
      = ∫ y in fundamentalDomain Γ, ∫ u, conj (w (mk Γ y)) * Ψ u y ∂lam ∂μ := by
        simp only [Φ, integral_const_mul]
    _ = ∫ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ ∂lam :=
        (integral_integral_swap hint).symm
    _ = 0 := by
        have h0 : ∀ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ = 0 := by
          intro u
          rw [← inner_eq_setIntegral_of_ae Γ μ w (v u) (hvr u)]
          exact Submodule.inner_left_of_mem_orthogonal (hvτ u) hw
        simp [h0]

end Gen

theorem UpperTheory.reps_integral_mem_closed_submodule :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)), IsClosed (τ : Set (L2 μ)) →
      ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G1 K n → ℂ),
        Continuous (fun p : U × G1 K n => Ψ p.1 p.2) → (∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C) → (∀ u, ∀ γ ∈ Gam K n, ∀ m, Ψ u (γ * m) = Ψ u m) → (∀ u, ∃ v ∈ τ, Reps μ v (Ψ u)) →
        ∃ v ∈ τ, Reps μ v fun m => ∫ u, Ψ u m ∂lam := by
  intro K _ _ n μ _ τ hτ U _ _ _ _ lam _ Ψ hc hb hinv hrep
  haveI : IsFiniteMeasure (quotientMeasure (Gam K n) μ) :=
    isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact closed_stable (Gam K n) μ τ hτ U lam Ψ hc hb hinv hrep
