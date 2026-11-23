import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Det

theorem volume_det_fin_two_eq_zero :
    MeasureTheory.volume {h : Fin 2 → Fin 2 → ℝ | (Matrix.of h).det = 0} = 0 := by
  classical
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
    {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hSm : MeasurableSet S := by
    have : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 0 * p.2 1 - p.1 1 * p.2 0) := by
      fun_prop
    exact this (measurableSet_singleton (0 : ℝ))
  have hnull : (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ))) S = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hSm]
    have h0 : ∀ᵐ a : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), a ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h0] with a ha
    let f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
      (a 0) • LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
        - (a 1) • LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
    have hk : LinearMap.ker f ≠ ⊤ := by
      intro htop
      have hf : f = 0 := LinearMap.ker_eq_top.mp htop
      apply ha
      funext i
      fin_cases i
      · have := LinearMap.congr_fun hf (Pi.single 1 1)
        simpa [f] using this
      · have := LinearMap.congr_fun hf (Pi.single 0 1)
        simpa [f] using this
    have hset : Prod.mk a ⁻¹' S = (LinearMap.ker f : Set (Fin 2 → ℝ)) := by
      ext b
      simp [hS, f]
    simp only [Pi.zero_apply]
    rw [hset]
    exact Measure.addHaar_submodule _ _ hk
  have hmp := volume_preserving_finTwoArrow (Fin 2 → ℝ)
  have hpre : {h : Fin 2 → Fin 2 → ℝ | (Matrix.of h).det = 0}
      = (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ)) ⁻¹' S := by
    ext h
    simp [hS, Matrix.det_fin_two, MeasurableEquiv.finTwoArrow]
  rw [hpre, hmp.measure_preimage hSm.nullMeasurableSet]
  exact hnull

end GlobalTheory.CompanionTheory.Det
