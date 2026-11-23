import Mathlib

open MeasureTheory

private theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral
    {X P E F : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : P × E → F)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P ↦ ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  haveI : ProperSpace P := FiniteDimensional.proper_real P
  have hc : Continuous Ψ := hΨ.continuous
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hD : Continuous fun z : P × E ↦
      (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
    (hΨ.continuous_fderiv (by simp)).clm_comp continuous_const
  have hcomp : IsCompact (Metric.closedBall p₀ 1 ×ˢ (a '' K)) :=
    (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hD.continuousOn
  have hsec : ∀ p : P, Continuous fun x : X ↦ (p, a x) := fun p ↦ continuous_const.prodMk ha
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x ↦ Ψ (p, a x))
    (F' := fun p x ↦ (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ ↦ C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p ↦
      ((hc.comp (hsec p)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · exact (hc.comp (hsec p₀)).continuousOn.integrableOn_compact hK
  · exact ((hD.comp (hsec p₀)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx p hp
    exact hC (p, a x) ⟨hp, Set.mem_image_of_mem a hx⟩
  · exact (continuous_const (y := C)).continuousOn.integrableOn_compact hK
  · refine Filter.Eventually.of_forall fun x p _ ↦ ?_
    exact (hd (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.contDiff_setIntegral_nat :
    ∀ {X P E : Type} [inst : TopologicalSpace X] [T2Space X]
    [inst_2 : MeasurableSpace X] [BorelSpace X] [inst_4 : NormedAddCommGroup P] [inst_5 : NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [inst_7 : NormedAddCommGroup E] [inst_8 : NormedSpace ℝ E] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] {K : Set X},
    IsCompact K →
      ∀ {a : X → E},
        Continuous a →
          ∀ (m : ℕ) {F : Type} [inst : NormedAddCommGroup F] [inst_10 : NormedSpace ℝ F] [CompleteSpace F]
            (Ψ : P × E → F),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
              ContDiff ℝ (↑m : WithTop ℕ∞) fun (p : P) ↦ ∫ (x : X) in K, Ψ (p, a x) ∂μ := by
  intro X P E _ _ _ _ _ _ _ _ _ μ _ K hK a ha m
  induction m with
  | zero =>
    intro F _ _ _ Ψ hΨ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p ↦
      (UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p).continuousAt
  | succ n ih =>
    intro F _ _ _ Ψ hΨ
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : P × E ↦
        (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
      (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ih _ hD, fun p ↦ UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p⟩
