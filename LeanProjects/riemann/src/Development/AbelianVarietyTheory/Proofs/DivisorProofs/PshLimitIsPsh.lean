import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

namespace GlobalTheory

open MeasureTheory Filter Topology Real

theorem isPsh_of_tendsto_of_locally_bounded_above :
    ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (ψ : ℕ → (Fin D → ℂ) → ℝ)
      (V : ℕ → Set (Fin D → ℂ)), IsOpen U → UpperSemicontinuousOn φ U →
      (∀ n, ReciprocityTheory.AnForm.A.IsPsh (V n) (ψ n)) →
      (∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → ∃ N : ℕ, ∃ M : ℝ, ∀ n, N ≤ n →
        K ⊆ V n ∧ ∀ z ∈ K, ψ n z ≤ M) →
      (∀ z ∈ U, Filter.Tendsto (fun n => ψ n z) Filter.atTop (nhds (φ z))) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro D U φ ψ V _hU hφ hψ hK hlim
  refine ⟨hφ, fun z w hdisc => ?_⟩
  have hγc : Continuous (fun ζ : ℂ => z + ζ • w) := by fun_prop
  set K := (fun ζ : ℂ => z + ζ • w) '' Metric.closedBall (0 : ℂ) 1 with hKdef
  have hKc : IsCompact K := (isCompact_closedBall 0 1).image hγc
  have hKU : K ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hdisc ζ (by simpa using hζ)
  obtain ⟨N, M, hNM⟩ := hK K hKc hKU
  have hmemK : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ K := fun ζ hζ => ⟨ζ, by simpa using hζ, rfl⟩
  have hcirc : ∀ θ : ℝ, ‖circleMap (0 : ℂ) 1 θ‖ ≤ 1 := fun θ => by simp [norm_circleMap_zero]
  have hψn : ∀ n, CircleIntegrable (fun ζ : ℂ => ψ (n + N) (z + ζ • w)) 0 1 ∧
      ψ (n + N) z ≤ Real.circleAverage (fun ζ : ℂ => ψ (n + N) (z + ζ • w)) 0 1 :=
    fun n => (hψ (n + N)).2 z w fun ζ hζ => (hNM (n + N) (by omega)).1 (hmemK ζ hζ)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)) with hμ
  set F : ℕ → ℝ → ℝ := fun n θ => ψ (n + N) (z + circleMap 0 1 θ • w) with hF
  set f : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w) with hf
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).1 (hψn n).1
  have hFle : ∀ n θ, F n θ ≤ M := fun n θ =>
    (hNM (n + N) (by omega)).2 _ (hmemK _ (hcirc θ))
  have hFlim : ∀ θ, Tendsto (fun n => F n θ) atTop (𝓝 (f θ)) := fun θ =>
    (hlim _ (hKU (hmemK _ (hcirc θ)))).comp (tendsto_add_atTop_nat N)
  have hz0 : z ∈ K := by simpa using hmemK 0 (by simp)
  have hzlim : Tendsto (fun n => ψ (n + N) z) atTop (𝓝 (φ z)) :=
    (hlim z (hKU hz0)).comp (tendsto_add_atTop_nat N)
  have hφzM : φ z ≤ M := le_of_tendsto' hzlim fun n => (hNM (n + N) (by omega)).2 z hz0
  have hfmeas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hFint n).aestronglyMeasurable)
      (ae_of_all _ hFlim)
  have hμuniv : μ.real Set.univ = 2 * π := by
    show (μ Set.univ).toReal = _
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring

  have hsub : ∀ n, 2 * π * ψ (n + N) z ≤ ∫ θ, F n θ ∂μ := by
    intro n
    have h := (hψn n).2
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le hpi.le, smul_eq_mul] at h
    have := mul_le_mul_of_nonneg_left h hpi.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at this
  have hlin : ∀ n, ∫⁻ θ, ENNReal.ofReal (M - F n θ) ∂μ ≤
      ENNReal.ofReal (2 * π * M - 2 * π * ψ (n + N) z) := by
    intro n
    have hi : Integrable (fun θ => M - F n θ) μ := (integrable_const M).sub (hFint n)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun θ => sub_nonneg.2 (hFle n θ))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub (integrable_const M) (hFint n), integral_const, smul_eq_mul, hμuniv]
    linarith [hsub n]
  have hfatou : ∫⁻ θ, ENNReal.ofReal (M - f θ) ∂μ ≤ ENNReal.ofReal (2 * π * M - 2 * π * φ z) := by
    have hlimR : Tendsto (fun n => ENNReal.ofReal (2 * π * M - 2 * π * ψ (n + N) z)) atTop
        (𝓝 (ENNReal.ofReal (2 * π * M - 2 * π * φ z))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub (hzlim.const_mul _))
    calc ∫⁻ θ, ENNReal.ofReal (M - f θ) ∂μ
        = ∫⁻ θ, liminf (fun n => ENNReal.ofReal (M - F n θ)) atTop ∂μ := by
          congr 1; ext θ
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.sub (hFlim θ))).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ θ, ENNReal.ofReal (M - F n θ) ∂μ) atTop :=
          lintegral_liminf_le' fun n =>
            (ENNReal.measurable_ofReal.comp_aemeasurable
              ((integrable_const M).sub (hFint n)).aemeasurable)
      _ ≤ liminf (fun n => ENNReal.ofReal (2 * π * M - 2 * π * ψ (n + N) z)) atTop :=
          liminf_le_liminf (Eventually.of_forall hlin)
      _ = _ := hlimR.liminf_eq
  have hfle : ∀ θ, f θ ≤ M := fun θ => le_of_tendsto' (hFlim θ) fun n => hFle n θ
  have hgnn : 0 ≤ᵐ[μ] fun θ => M - f θ := ae_of_all _ fun θ => sub_nonneg.2 (hfle θ)
  have hgint : Integrable (fun θ => M - f θ) μ := by
    refine ⟨aestronglyMeasurable_const.sub hfmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hgnn]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hfint : Integrable f μ := by
    have := (integrable_const M).sub hgint
    refine this.congr (ae_of_all _ fun θ => ?_)
    simp
  have hgle : ∫ θ, (M - f θ) ∂μ ≤ 2 * π * M - 2 * π * φ z := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hgint hgnn
    rw [← h1] at hfatou
    exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 hfatou
  have hfge : 2 * π * φ z ≤ ∫ θ, f θ ∂μ := by
    rw [integral_sub (integrable_const M) hfint, integral_const, smul_eq_mul, hμuniv] at hgle
    linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).2 hfint, ?_⟩
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le hpi.le, smul_eq_mul]
  rw [le_inv_mul_iff₀ hpi]
  exact hfge

end GlobalTheory
