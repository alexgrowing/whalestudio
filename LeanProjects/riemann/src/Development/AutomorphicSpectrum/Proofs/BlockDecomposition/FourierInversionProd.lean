import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open scoped FourierTransform

namespace GlobalTheory.CompanionTheory.TubeFourier

def planeCoord : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem planeCoord_apply (v : EuclideanSpace ℝ (Fin 2)) : planeCoord v = (v 0, v 1) := rfl

theorem continuous_planeCoord : Continuous planeCoord := by
  rw [show (planeCoord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun v => (v 0, v 1) from funext planeCoord_apply]
  fun_prop

theorem measurePreserving_planeCoord : MeasurePreserving planeCoord volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem inner_eq_rdot (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = rdot (planeCoord v) (planeCoord w) := by
  rw [planeCoord_apply, planeCoord_apply]
  simp [rdot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem fourier_comp_planeCoord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℝ × ℝ → X) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v => h (planeCoord v)) w =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y := by
  rw [Real.fourier_eq', ← measurePreserving_planeCoord.integral_comp'
    (fun y : ℝ × ℝ => Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y)]
  congr 1
  ext v
  rw [inner_eq_rdot]
  congr 2
  simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

theorem fourier_inversion_prod : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  intro X _ _ _ h hc hi hT y
  set T : ℝ × ℝ → X := fun t => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y with hTdef
  set f : EuclideanSpace ℝ (Fin 2) → X := fun v => h (planeCoord v) with hf
  have hfc : Continuous f := hc.comp continuous_planeCoord
  have hfi : Integrable f :=
    (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr hi
  have hFf : ∀ w, 𝓕 f w = T ((2 * Real.pi) • planeCoord w) := fun w => fourier_comp_planeCoord h w
  have hFi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => T ((2 * Real.pi) • planeCoord w) from funext hFf]
    have h1 : Integrable (fun t : ℝ × ℝ => T ((2 * Real.pi) • t)) := hT.comp_smul (by positivity)
    exact (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr h1
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) (planeCoord.symm y)
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (f := fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) (R := 2 * Real.pi)
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hrank] at hsub
  have hlhs : 𝓕⁻ (𝓕 f) (planeCoord.symm y) = ∫ s : ℝ × ℝ,
      (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s) := by
    rw [Real.fourierInv_eq', ← measurePreserving_planeCoord.integral_comp'
      (fun s : ℝ × ℝ => (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s))]
    congr 1
    ext w
    simp only [hFf, inner_eq_rdot, MeasurableEquiv.apply_symm_apply]
    congr 2
    simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    ring
  rw [hinv] at hlhs
  have hy : h y = f (planeCoord.symm y) := by simp [hf]
  rw [hy, hlhs, hsub, abs_of_pos (by positivity), ← Complex.coe_smul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.TubeFourier
