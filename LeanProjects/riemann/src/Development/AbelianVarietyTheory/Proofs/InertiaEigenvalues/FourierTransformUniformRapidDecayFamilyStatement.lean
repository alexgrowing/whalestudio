import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransform_uniformRapidDecay_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (ι : Type) (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)), (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) → (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) → ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  first | exact @GlobalTheory.fourier_decay_family | exact GlobalTheory.fourier_decay_family | (intros; apply GlobalTheory.fourier_decay_family <;> assumption)
