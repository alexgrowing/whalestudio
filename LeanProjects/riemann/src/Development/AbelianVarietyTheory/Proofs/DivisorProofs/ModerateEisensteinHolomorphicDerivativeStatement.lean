import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_eisenstein_holomorphic_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    ∀ z : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      GlobalTheory.UAut.dop z (fun g => circleIntegral (fun w => (w - s₀) ^ j * H₀ w g) s₀ r) g =
        circleIntegral (fun w => (w - s₀) ^ j * GlobalTheory.UAut.dop z (H₀ w) g) s₀ r := by
  first | exact @GlobalTheory.CircleDop.dop_circleIntegral | exact GlobalTheory.CircleDop.dop_circleIntegral | (intros; apply GlobalTheory.CircleDop.dop_circleIntegral <;> assumption)
