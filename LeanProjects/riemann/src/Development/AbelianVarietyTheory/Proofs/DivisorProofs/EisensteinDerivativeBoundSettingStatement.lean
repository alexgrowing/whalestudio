import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDerivativeBoundSetting
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
theorem _root_.GlobalTheory.T.eisenstein_derivative_bound_setting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 (((n : ℂ) - 1) / 2) → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H s g = (s - (((n : ℂ) - 1) / 2)) ^ k * Eis s g) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∃ (C : ℝ) (N : ℕ), ∀ s ∈ V, ∀ g, ‖H s g‖ ≤ C * (height σ J g : ℝ) ^ N := by
  first | exact @GlobalTheory.EisRes.laurentMul_locally_uniform_moderate | exact GlobalTheory.EisRes.laurentMul_locally_uniform_moderate | (intros; apply GlobalTheory.EisRes.laurentMul_locally_uniform_moderate <;> assumption)
