import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

open MeasureTheory Filter Set GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AutomorphicL2Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {f : G → ℂ}

theorem integrableOn_rmul (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    IntegrableOn (fun q => F (rmul Γ y q)) s (quotMeasure Γ μ) :=
  (integrableOn_Lp_of_measure_ne_top (R Γ μ y F) (by norm_num) hs).congr (ae_restrict_of_ae (coeFn_R y F))

theorem setIntegral_norm_rmul_le (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    ∫ q in s, ‖F (rmul Γ y q)‖ ∂quotMeasure Γ μ ≤
      (quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ := by
  have h2 : Integrable (fun q => ‖F q‖ ^ 2) (quotMeasure Γ μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have h3 : Integrable (fun q => ‖F (rmul Γ y q)‖ ^ 2) (quotMeasure Γ μ) :=
    ((measurePreserving_rmul y).integrable_comp h2.1).2 h2
  have h4 : ∫ q, ‖F (rmul Γ y q)‖ ^ 2 ∂quotMeasure Γ μ = ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ := by
    have h := integral_map (μ := quotMeasure Γ μ) (measurable_rmul (Γ := Γ) y).aemeasurable
      (f := fun q => ‖F q‖ ^ 2) (by rw [(measurePreserving_rmul y).map_eq]; exact h2.1)
    rw [(measurePreserving_rmul y).map_eq] at h
    exact h.symm
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) s (quotMeasure Γ μ) := integrableOn_const hs
  calc ∫ q in s, ‖F (rmul Γ y q)‖ ∂quotMeasure Γ μ
      ≤ ∫ q in s, (1 + ‖F (rmul Γ y q)‖ ^ 2) ∂quotMeasure Γ μ :=
        integral_mono (integrableOn_rmul F y hs).norm (Integrable.add h1 h3.integrableOn) fun q => by
          beta_reduce
          nlinarith [sq_nonneg (‖F (rmul Γ y q)‖ - 1), norm_nonneg (F (rmul Γ y q))]
    _ = (quotMeasure Γ μ).real s + ∫ q in s, ‖F (rmul Γ y q)‖ ^ 2 ∂quotMeasure Γ μ := by
        rw [integral_add h1 h3.integrableOn]
        simp
    _ ≤ _ := by
        rw [← h4]
        exact add_le_add le_rfl (setIntegral_le_integral h3 (.of_forall fun q => by positivity))

variable [SigmaFinite μ]

theorem integrable_prod (hf : Integrable f μ) (F : L2 Γ μ) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    Integrable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1)) (((quotMeasure Γ μ).restrict s).prod μ) := by
  have hm : AEStronglyMeasurable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1))
      (((quotMeasure Γ μ).restrict s).prod μ) :=
    hf.1.comp_snd.mul ((Lp.stronglyMeasurable F).comp_measurable measurable_rmul_uncurry).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨.of_forall fun y => (integrableOn_rmul F y hs).const_mul (f y), ?_⟩
  refine (hf.norm.mul_const ((quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ)).mono'
    hm.norm.prod_swap.integral_prod_right' (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (setIntegral_norm_rmul_le F y hs) (norm_nonneg _)

theorem ae_integrable (hf : Integrable f μ) (F : L2 Γ μ) :
    ∀ᵐ q ∂quotMeasure Γ μ, Integrable (fun y => f y * F (rmul Γ y q)) μ :=
  ae_of_forall_measure_lt_top_ae_restrict _ fun _ _ hs => (integrable_prod hf F hs.ne).prod_right_ae

theorem coeFn_Rop [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] (hf : Integrable f μ) (F : L2 Γ μ) :
    Rop Γ μ f F =ᵐ[quotMeasure Γ μ] fun q => ∫ y, f y * F (rmul Γ y q) ∂μ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
    (fun s _ hs => (integrable_prod hf F hs.ne).integral_prod_left) fun s hs hfin => ?_
  have hR := isRepOp_Rop (Γ := Γ) hf F
  rw [integral_integral_swap (f := fun q y => f y * F (rmul Γ y q)) (integrable_prod hf F hfin.ne),
    ← L2.inner_indicatorConstLp_one hs hfin.ne, hR.2]
  refine (integral_inner (𝕜 := ℂ) hR.1 _).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
  beta_reduce
  rw [inner_smul_right, L2.inner_indicatorConstLp_one hs hfin.ne, integral_const_mul,
    integral_congr_ae (ae_restrict_of_ae (coeFn_R y F))]

theorem lift_Rop_eq_convR (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ f : G → ℂ, Integrable f μ → ∀ F : L2 Γ μ,
      (∀ᵐ x ∂μ, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧
        lift Γ (Rop Γ μ f F) =ᵐ[μ] convR μ f (lift Γ F) :=
  fun _ hf F => ⟨ae_quotMeasure_iff.1 (ae_integrable hf F), ae_quotMeasure_iff.1 (coeFn_Rop hf F)⟩

end GlobalTheory.AutomorphicL2Pointwise
