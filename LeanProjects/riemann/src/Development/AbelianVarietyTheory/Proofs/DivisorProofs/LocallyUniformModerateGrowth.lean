import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.WeakHolFamily

theorem locally_uniform_moderate_growth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (H : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (U : Set ℂ), U ∈ 𝓝 s₀ →
    (∀ s ∈ U, IsSmoothModerate σ J (H s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) →
    ∃ V ∈ 𝓝 s₀, ∃ (C : ℝ) (N : ℕ), ∀ s ∈ V, ∀ g, ‖H s g‖ ≤ C * (height σ J g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ n J H s₀ U hU hH hμ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (interior_mem_nhds.2 hU)
  have hD : Metric.closedBall s₀ (ε / 2) ⊆ interior U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨-, N, C, hC⟩ := word_holomorphic_and_uniform F E σ n J H (interior U) (Metric.closedBall s₀ (ε / 2))
    isOpen_interior (isCompact_closedBall s₀ (ε / 2)) hD (fun s hs => hH s (interior_subset hs))
    (fun μ hm => (hμ μ hm).mono interior_subset) [] (by simp)
  exact ⟨Metric.closedBall s₀ (ε / 2), Metric.closedBall_mem_nhds s₀ (by linarith), C, N,
    fun s hs g => by simpa using hC s hs g⟩

end GlobalTheory.WeakHolFamily
