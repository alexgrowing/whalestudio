import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.DetC

theorem volume_det_fin_two_complex_eq_zero :
    volume {h : Ad3.K.LC.M22 | (Matrix.of h).det = 0} = 0 := by
  classical
  set S : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
    {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hSm : MeasurableSet S := by
    have : Measurable (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) => p.1 0 * p.2 1 - p.1 1 * p.2 0) := by
      fun_prop
    exact this (measurableSet_singleton (0 : ℂ))
  have hnull : (volume : Measure ((Fin 2 → ℂ) × (Fin 2 → ℂ))) S = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hSm]
    have h0 : ∀ᵐ a : Fin 2 → ℂ ∂(volume : Measure (Fin 2 → ℂ)), a ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h0] with a ha
    let f : (Fin 2 → ℂ) →ₗ[ℝ] ℂ :=
      (((a 0) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1
        - (a 1) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0 :
          (Fin 2 → ℂ) →ₗ[ℂ] ℂ)).restrictScalars ℝ
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
    have hset : Prod.mk a ⁻¹' S = (LinearMap.ker f : Set (Fin 2 → ℂ)) := by
      ext b
      simp [hS, f]
    simp only [Pi.zero_apply]
    rw [hset]
    exact Measure.addHaar_submodule _ _ hk
  have hmp := volume_preserving_finTwoArrow (Fin 2 → ℂ)
  have hpre : {h : Ad3.K.LC.M22 | (Matrix.of h).det = 0}
      = (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℂ)) ⁻¹' S := by
    ext h
    simp [hS, Matrix.det_fin_two, MeasurableEquiv.finTwoArrow]
  rw [hpre, hmp.measure_preimage hSm.nullMeasurableSet]
  exact hnull

end GlobalTheory.CompanionTheory.DetC
