import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.admitted

section

variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem integrable_cont {F : Type} [NormedAddCommGroup F] {f : K → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem exists_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ k, e k • σ k u ∂μ
      map_add' := fun u w => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_cont (he.smul (hc u))) (integrable_cont (he.smul (hc w)))
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

end

theorem exists_averaging_operator : ExistsAvg := by
  intro K _ _ _ _ _ _ _ _ μ _ _ H _ _ _ σ hiso hc S _ hS v hv
  have hcoef : ∀ a b : H, Continuous fun x => ⟪σ x a, b⟫_ℂ := fun a b => (hc a).inner continuous_const
  have hint : ∀ b : H, Integrable (fun x => ⟪σ x v, b⟫_ℂ • σ x v) μ := fun b =>
    integrable_cont ((hcoef v b).smul (hc v))
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : H →ₗ[ℂ] H :=
    { toFun := fun b => ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  have hinner : ∀ w b, ⟪w, L b⟫_ℂ = ∫ x, ⟪σ x v, b⟫_ℂ * ⟪w, σ x v⟫_ℂ ∂μ := by
    intro w b
    change ⟪w, ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ⟫_ℂ = _
    rw [← integral_inner (hint b)]
    simp only [inner_smul_right]
  have hLS : ∀ b, L b ∈ S := by
    intro b
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hinner]
    have : ∀ x, ⟪w, σ x v⟫_ℂ = 0 := fun x => Submodule.inner_left_of_mem_orthogonal (hS x v hv) hw
    simp [this]
  have hzero : ∀ w, ⟪w, L w⟫_ℂ = 0 → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [hinner] at hw
    have e1 : ∀ x, ⟪σ x v, w⟫_ℂ * ⟪w, σ x v⟫_ℂ = ((‖⟪σ x v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← inner_conj_symm w, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1] at hw
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
    have hcont : Continuous fun x => ‖⟪σ x v, w⟫_ℂ‖ ^ 2 := (hcoef v w).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (integrable_cont hcont)).1 hw
    have h2 : ‖⟪σ 1 v, w⟫_ℂ‖ ^ 2 = 0 := congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 h1) 1
    simp only [map_one, ContinuousLinearMap.one_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact inner_eq_zero_symm.1 h2
  set R : Submodule ℂ H := S.map L with hR
  have hRc : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hvR : v ∈ R := by
    set w := v - R.starProjection v with hw
    have hwo : w ∈ Rᗮ := R.sub_starProjection_mem_orthogonal v
    have hp : R.starProjection v ∈ R := R.starProjection_apply_mem v
    have hRS : R ≤ S := by rintro _ ⟨b, -, rfl⟩; exact hLS b
    have hwS : w ∈ S := S.sub_mem hv (hRS hp)
    have h1 : ⟪w, v⟫_ℂ = 0 := hzero w (Submodule.inner_left_of_mem_orthogonal (K := R) (Submodule.mem_map_of_mem hwS) hwo)
    have h2 : ⟪w, R.starProjection v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hwo
    have h3 : ⟪w, w⟫_ℂ = 0 := by
      conv_lhs => rw [hw, inner_sub_right, ← hw]
      rw [h1, h2, sub_zero]
    rw [inner_self_eq_zero, hw, sub_eq_zero] at h3
    rw [h3]; exact hp
  obtain ⟨b, -, hb⟩ := hvR
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc (hcoef v b)
  refine ⟨fun x => ⟪σ x v, b⟫_ℂ, E, hcoef v b, ?_, hE, by rw [hE]; exact hb⟩
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => ⟪σ x (B i), b⟫_ℂ, fun i => hcoef _ b, fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ v = ∑ i, B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ v, hS _ v hv⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show ⟪σ (x * k⁻¹) v, b⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left]

end CompanionTheory.D.gk.admitted
