import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsKernelProjMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace KernelProjMeasurable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

def shifted (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ContinuousLinearMap.adjoint A) ∘L A + (ε : ℂ) • (1 : E →L[ℂ] E)

theorem re_inner_shifted (A : E →L[ℂ] F) (ε : ℝ) (u : E) :
    RCLike.re (inner ℂ u (shifted A ε u)) = ‖A u‖ ^ 2 + ε * ‖u‖ ^ 2 := by
  simp only [shifted, add_apply, comp_apply, smul_apply, one_apply, inner_add_right,
    inner_smul_right, adjoint_inner_right, inner_self_eq_norm_sq_to_K, map_add]
  simp [← Complex.ofReal_pow]

theorem inner_shifted_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by
  simp [shifted, inner_add_right, inner_smul_right, adjoint_inner_right, hz]

theorem shifted_apply_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by
  simp [shifted, hz]

theorem mul_norm_le_norm_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) (u : E) :
    ε * ‖u‖ ≤ ‖shifted A ε u‖ := by
  have h1 := re_inner_shifted A ε u
  have h2 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · have h3 : (ε * ‖u‖) * ‖u‖ ≤ ‖shifted A ε u‖ * ‖u‖ := by
      nlinarith [sq_nonneg ‖A u‖]
    exact le_of_mul_le_mul_right h3 h

theorem isUnit_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) : IsUnit (shifted A ε) := by
  have hinj : Function.Injective (shifted A ε : E →ₗ[ℂ] E) := by
    intro a b hab
    have h := mul_norm_le_norm_shifted A hε (a - b)
    have hab' : shifted A ε a = shifted A ε b := hab
    rw [map_sub, hab', sub_self, norm_zero] at h
    have h0 : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv.toUnit, ?_⟩
  ext v
  rfl

theorem exists_norm_le_norm_shifted (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  have hinj : Function.Injective ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (u : E) ∈ K := hu
    have h2 : (u : E) ∈ K ⊓ Kᗮ := ⟨h1, u.2⟩
    rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨c, -, hc⟩ := ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype).injective_iff_antilipschitz.1 hinj
  refine ⟨(c : ℝ) ^ 2, sq_nonneg _, fun ε hε u hu => ?_⟩
  have h1 : ‖u‖ ≤ c * ‖A u‖ := by
    simpa using hc.le_mul_norm (map_zero _) ⟨u, hu⟩
  have h2 := re_inner_shifted A ε u
  have h3 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  have hc0 : (0 : ℝ) ≤ c := c.2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have hAu : ‖u‖ ^ 2 ≤ (c : ℝ) ^ 2 * ‖A u‖ ^ 2 := by
      have := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      nlinarith
    have h4 : (c : ℝ) ^ 2 * ‖A u‖ ^ 2 ≤ (c : ℝ) ^ 2 * (‖u‖ * ‖shifted A ε u‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [mul_nonneg hε (sq_nonneg ‖u‖)]
    have h5 : ‖u‖ * ‖u‖ ≤ ((c : ℝ) ^ 2 * ‖shifted A ε u‖) * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 h

def resolvent (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ε : ℂ) • Ring.inverse (shifted A ε)

theorem exists_norm_resolvent_sub_le (A : E →L[ℂ] F) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_norm_shifted A
  refine ⟨2 * C, fun ε hε => ?_⟩
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := (resolvent A ε - K.starProjection) v with hu_def
  have hinv : shifted A ε (Ring.inverse (shifted A ε) v) = v := by
    have := Ring.mul_inverse_cancel _ (isUnit_shifted A hε)
    exact congrArg (fun T : E →L[ℂ] E => T v) this
  have hPv : A (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hTu : shifted A ε u = (ε : ℂ) • (v - K.starProjection v) := by
    rw [hu_def, resolvent, sub_apply, smul_apply, map_sub, map_smul, hinv,
      shifted_apply_of_apply_eq_zero A ε hPv, smul_sub]
  have hu : u ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 := inner_shifted_of_apply_eq_zero A ε u hz
    rw [hTu, inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 (K.sub_starProjection_mem_orthogonal v) z hz, mul_zero] at h1
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hε'
  have hvP : ‖v - K.starProjection v‖ ≤ 2 * ‖v‖ :=
    (norm_sub_le _ _).trans (by linarith [K.norm_starProjection_apply_le v])
  calc ‖u‖ ≤ C * ‖shifted A ε u‖ := hCb ε hε.le u hu
    _ = C * (ε * ‖v - K.starProjection v‖) := by
      rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ C * (ε * (2 * ‖v‖)) := by gcongr
    _ = 2 * C * ε * ‖v‖ := by ring

theorem tendsto_resolvent (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by
  obtain ⟨C, hC⟩ := exists_norm_resolvent_sub_le A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hC _ (by positivity)) ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

theorem continuous_resolvent {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by
  have hadj : Continuous fun x => ContinuousLinearMap.adjoint (A x) :=
    ContinuousLinearMap.adjoint.continuous.comp hA
  have hT : Continuous fun x => shifted (A x) ε := by
    simp only [shifted]
    exact (hadj.clm_comp hA).add continuous_const
  have hI : Continuous fun x => Ring.inverse (shifted (A x) ε) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h := NormedRing.inverse_continuousAt (isUnit_shifted (A x) hε).unit
    rw [IsUnit.unit_spec] at h
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun x => shifted (A x) ε) h hT.continuousAt
  show Continuous fun x => (ε : ℂ) • Ring.inverse (shifted (A x) ε)
  exact hI.const_smul (ε : ℂ)

end KernelProjMeasurable

theorem KernelProjMeasurable.proof : KernelProjMeasurable.Statement := by
  intro X _ _ _ n k L hL
  let A : X → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
    fun x => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L x))
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro v
    change Continuous fun x => (WithLp.toLp 2 (Matrix.mulVec (L x) (WithLp.ofLp v)) : EuclideanSpace ℂ (Fin k))
    exact (PiLp.continuous_toLp 2 _).comp (hL.matrix_mulVec continuous_const)
  refine measurable_of_tendsto_metrizable
    (f := fun j x => KernelProjMeasurable.resolvent (A x) (1 / ((j : ℝ) + 1)))
    (fun j => (KernelProjMeasurable.continuous_resolvent hA (by positivity)).measurable) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact KernelProjMeasurable.tendsto_resolvent (A x)

end

end GroundTheory.Heights₂.Heights
