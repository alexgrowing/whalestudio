import Mathlib
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection

namespace GroundTheory.Automorphic

namespace UnitaryRep

open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)

lemma aestronglyMeasurable_inner_orbit (w v : H) :
    AEStronglyMeasurable (fun g => ⟪w, π g v⟫_ℂ) μ :=
  (continuous_const.inner (π.continuous_orbit v)).aestronglyMeasurable

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
lemma norm_inner_orbit_le (w v : H) (g : G) : ‖⟪w, π g v⟫_ℂ‖ ≤ ‖w‖ * ‖v‖ := by
  calc ‖⟪w, π g v⟫_ℂ‖ ≤ ‖w‖ * ‖π g v‖ := norm_inner_le_norm _ _
    _ = ‖w‖ * ‖v‖ := by rw [norm_map]

lemma integrable_mul_inner_orbit (f : G →₁[μ] ℂ) (w v : H) :
    Integrable (fun g => f g * ⟪w, π g v⟫_ℂ) μ :=
  (L1.integrable_coeFn f).mul_bdd (π.aestronglyMeasurable_inner_orbit μ w v)
    (Eventually.of_forall fun g => π.norm_inner_orbit_le w v g)

omit [OpensMeasurableSpace G] in
lemma norm_integral_mul_inner_orbit_le (f : G →₁[μ] ℂ) (w v : H) :
    ‖∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ‖ ≤ ‖f‖ * ‖w‖ * ‖v‖ := by
  calc ‖∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖w‖ * ‖v‖) ∂μ :=
        norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
          (Eventually.of_forall fun g => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (π.norm_inner_orbit_le w v g) (norm_nonneg _))
    _ = ‖f‖ * ‖w‖ * ‖v‖ := by rw [integral_mul_const, L1.norm_eq_integral_norm, mul_assoc]

noncomputable def integratedForm (f : G →₁[μ] ℂ) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun w v => ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ)
      (fun w₁ w₂ v => by
        simp only [inner_add_left, mul_add]
        exact integral_add (π.integrable_mul_inner_orbit μ f w₁ v)
          (π.integrable_mul_inner_orbit μ f w₂ v))
      (fun c w v => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; ring)
      (fun w v₁ v₂ => by
        simp only [map_add, inner_add_right, mul_add]
        exact integral_add (π.integrable_mul_inner_orbit μ f w v₁)
          (π.integrable_mul_inner_orbit μ f w v₂))
      (fun c w v => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; ext g; ring))
    ‖f‖ (fun w v => π.norm_integral_mul_inner_orbit_le μ f w v)

noncomputable def integratedOp (f : G →₁[μ] ℂ) : H →L[ℂ] H :=
  adjoint (InnerProductSpace.continuousLinearMapOfBilin (π.integratedForm μ f))

lemma inner_integratedOp (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, π.integratedOp μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  rw [integratedOp, adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

lemma norm_integratedOp_apply_le (f : G →₁[μ] ℂ) (v : H) :
    ‖π.integratedOp μ f v‖ ≤ ‖f‖ * ‖v‖ := by
  set x := π.integratedOp μ f v
  have h := π.norm_integral_mul_inner_orbit_le μ f x v
  rw [← inner_integratedOp] at h
  have h' : ‖x‖ * ‖x‖ ≤ ‖x‖ * (‖f‖ * ‖v‖) := by
    have e : ‖⟪x, x⟫_ℂ‖ = ‖x‖ * ‖x‖ := by rw [inner_self_eq_norm_sq_to_K]; simp [sq]
    rw [e] at h
    linarith
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_left h' hpos

noncomputable def integrated : (G →₁[μ] ℂ) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := π.integratedOp μ
      map_add' := fun f₁ f₂ => by
        refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
        rw [add_apply, inner_add_right, inner_integratedOp, inner_integratedOp,
          inner_integratedOp, ← integral_add (π.integrable_mul_inner_orbit μ f₁ w v)
            (π.integrable_mul_inner_orbit μ f₂ w v)]
        refine integral_congr_ae ((Lp.coeFn_add f₁ f₂).mono fun g hg => ?_)
        simp only [hg, Pi.add_apply, add_mul]
      map_smul' := fun c f => by
        refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
        rw [smul_apply, inner_smul_right, inner_integratedOp, inner_integratedOp,
          RingHom.id_apply, ← integral_const_mul]
        refine integral_congr_ae ((Lp.coeFn_smul c f).mono fun g hg => ?_)
        simp only [hg, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    1 (fun f => by
      rw [one_mul]
      exact opNorm_le_bound _ (norm_nonneg _) fun v => π.norm_integratedOp_apply_le μ f v)

theorem inner_integrated (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, π.integrated μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ :=
  π.inner_integratedOp μ f w v

theorem norm_integrated_apply_le (f : G →₁[μ] ℂ) (v : H) :
    ‖π.integrated μ f v‖ ≤ ‖f‖ * ‖v‖ :=
  π.norm_integratedOp_apply_le μ f v

theorem norm_integrated_le (f : G →₁[μ] ℂ) : ‖π.integrated μ f‖ ≤ ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun v => π.norm_integrated_apply_le μ f v

theorem integrated_apply_eq_integral (f : G →₁[μ] ℂ) (v : H)
    (hint : Integrable (fun g => f g • π g v) μ) :
    π.integrated μ f v = ∫ g, f g • π g v ∂μ := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_integrated, ← integral_inner hint]
  simp_rw [inner_smul_right]

theorem integrable_smul_orbit [SecondCountableTopologyEither G H] (f : G →₁[μ] ℂ) (v : H) :
    Integrable (fun g => f g • π g v) μ :=
  (L1.integrable_coeFn f).smul_bdd ‖v‖ (π.continuous_orbit v).aestronglyMeasurable
    (Eventually.of_forall fun g => (π.norm_map g v).le)

theorem integrated_apply [SecondCountableTopologyEither G H] (f : G →₁[μ] ℂ) (v : H) :
    π.integrated μ f v = ∫ g, f g • π g v ∂μ :=
  π.integrated_apply_eq_integral μ f v (π.integrable_smul_orbit μ f v)

theorem integrated_toLp_apply [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π.integrated μ ((f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).toLp f) v = ∫ g, f g • π g v ∂μ := by
  set hmem := f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1) f.hasCompactSupport
  have hae : ((hmem.toLp f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := hmem.coeFn_toLp
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      (f.hasCompactSupport.smul_right)
  have hint' : Integrable (fun g => (hmem.toLp f : G →₁[μ] ℂ) g • π g v) μ :=
    hint.congr (hae.mono fun g hg => by simp only [hg])
  rw [π.integrated_apply_eq_integral μ _ v hint']
  exact integral_congr_ae (hae.mono fun g hg => by simp only [hg])

theorem comp_integrated_of_mem_intertwiners {σ : UnitaryRep G K} {T : H →L[ℂ] K}
    (hT : T ∈ π.intertwiners σ) (f : G →₁[μ] ℂ) :
    T ∘L π.integrated μ f = σ.integrated μ f ∘L T := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [comp_apply, comp_apply, ← adjoint_inner_left, inner_integrated, inner_integrated]
  congr 1; ext g
  rw [adjoint_inner_left, hT]

theorem IsInvariant.integrated_mem {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (f : G →₁[μ] ℂ) {v : H} (hv : v ∈ V) :
    π.integrated μ f v ∈ V := by
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g =>
      ((isInvariant_iff_commute_starProjection V).mp hV g).symm
  have h := congrArg (fun T : H →L[ℂ] H => T v) (π.comp_integrated_of_mem_intertwiners μ hP f)
  simp only [comp_apply, Submodule.starProjection_eq_self_iff.mpr hv] at h
  rw [← h]
  exact V.starProjection_apply_mem _

theorem inner_adjoint_integrated (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, adjoint (π.integrated μ f) v⟫_ℂ = ∫ g, conj (f g) * ⟪w, π g⁻¹ v⟫_ℂ ∂μ := by
  rw [adjoint_inner_right, ← inner_conj_symm, inner_integrated, ← integral_conj]
  congr 1; ext g
  rw [_root_.map_mul, inner_conj_symm, inner_map_left]

section translate

variable [IsTopologicalGroup G] [BorelSpace G]

noncomputable def leftTranslate [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) : G →₁[μ] ℂ :=
  Lp.compMeasurePreserving (fun g => h⁻¹ * g) (measurePreserving_mul_left μ h⁻¹) f

omit [OpensMeasurableSpace G] in
lemma coeFn_leftTranslate [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    (leftTranslate μ h f : G → ℂ) =ᵐ[μ] fun g => f (h⁻¹ * g) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem map_comp_integrated [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    π h ∘L π.integrated μ f = π.integrated μ (leftTranslate μ h f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [comp_apply, inner_map_right, inner_integrated, inner_integrated]
  rw [integral_congr_ae ((coeFn_leftTranslate μ h f).mono fun g hg =>
    show (leftTranslate μ h f) g * ⟪w, π g v⟫_ℂ = f (h⁻¹ * g) * ⟪w, π g v⟫_ℂ by rw [hg])]
  rw [← integral_mul_left_eq_self (fun g => f (h⁻¹ * g) * ⟪w, π g v⟫_ℂ) h]
  congr 1; ext g
  rw [inv_mul_cancel_left, inner_map_left, inv_inv, map_mul_apply]

noncomputable def involution [μ.IsInvInvariant] (f : G →₁[μ] ℂ) : G →₁[μ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
    (Lp.compMeasurePreserving (fun g => g⁻¹) (Measure.measurePreserving_inv μ) f)

omit [OpensMeasurableSpace G] in
lemma coeFn_involution [μ.IsInvInvariant] (f : G →₁[μ] ℂ) :
    (involution μ f : G → ℂ) =ᵐ[μ] fun g => conj (f g⁻¹) := by
  have h1 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp
    (Lp.compMeasurePreserving (fun g => g⁻¹) (Measure.measurePreserving_inv μ) f)
  have h2 := Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_inv μ)
  filter_upwards [h1, h2] with g hg1 hg2
  rw [involution, hg1, hg2]
  rfl

theorem adjoint_integrated [μ.IsInvInvariant] (f : G →₁[μ] ℂ) :
    adjoint (π.integrated μ f) = π.integrated μ (involution μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [inner_adjoint_integrated, inner_integrated]
  rw [integral_congr_ae ((coeFn_involution μ f).mono fun g hg =>
    show (involution μ f) g * ⟪w, π g v⟫_ℂ = conj (f g⁻¹) * ⟪w, π g v⟫_ℂ by rw [hg])]
  rw [← integral_inv_eq_self (fun g => conj (f g⁻¹) * ⟪w, π g v⟫_ℂ) μ]
  simp only [inv_inv]

end translate

end UnitaryRep

end GroundTheory.Automorphic
