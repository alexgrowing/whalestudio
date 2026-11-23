import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinMeromorphicContinuation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_meromorphic_continuation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (b : ℕ) (Eis : ℂ → UA σ J → ℂ), GlobalTheory.ConeSmallCT.EisGood b Eis →
    (∀ s₀ : ℂ, ∀ γ ∈ ratU σ J, ∀ g, ∀ᶠ s in 𝓝[≠] s₀, Eis s (γ * g) = Eis s g) →
    (∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, Measurable (Eis s)) →
    (∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (Hol : ℂ → UA σ J → ℂ) (C : ℝ) (N : ℕ), 0 < r ∧
      (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧
      (∀ g, DifferentiableOn ℂ (Hol · g) (Metric.ball s₀ r)) ∧
      (∀ s ∈ Metric.ball s₀ r, ∀ g, ‖Hol s g‖ ≤ C * (qht g : ℝ) ^ N) ∧ ∀ s ∈ Metric.ball s₀ r, Measurable (Hol s)) ∧
    ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ (∀ g, DifferentiableOn ℂ (Eis · g) (Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r)) ∧
      (∀ s ∈ Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r, ∀ g, ‖Eis s g‖ ≤ C * (qht g : ℝ) ^ N) ∧
      ∀ s ∈ Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r, Measurable (Eis s) := by
  first | exact @GlobalTheory.ConeSmallCT.eisGood_qht_measurable | exact GlobalTheory.ConeSmallCT.eisGood_qht_measurable | (intros; apply GlobalTheory.ConeSmallCT.eisGood_qht_measurable <;> assumption)
