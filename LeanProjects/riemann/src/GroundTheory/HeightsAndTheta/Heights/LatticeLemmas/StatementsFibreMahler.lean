import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

def FibreMahlerForms.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (W : Type) [AddCommGroup W] [Module (𝓞 F) W]
    [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W] (h : HermitianMetric F W) (n : ℕ)
    (w : Fin n → W), Submodule.span (𝓞 F) (Set.range w) = ⊤ →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (τ : K →+* ℂ) (m : ℕ)
      (yv : Fin m → DualVec F W K), (∀ q, yv q ≠ 0) → ∀ a : ℂ, a ≠ 0 →
        fibreMahler h (τ.comp (algebraMap F K)) w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) =
          Real.log ‖a‖ + ∑ q, (Real.log (archDualNorm h τ (yv q)) -
            (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)

example : HermitianMetric ℚ (Fin 2 → 𝓞 ℚ) := HermitianMetric.standard ℚ (Fin 2)

end

end GroundTheory.Heights₂.Heights
