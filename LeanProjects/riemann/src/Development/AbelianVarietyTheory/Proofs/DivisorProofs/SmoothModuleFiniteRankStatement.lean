import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothModuleFiniteRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_module_finite_rank : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (A : Submodule ℂ (GAd σ J → ℂ)) (K : Set (GAd σ J)), (∀ k ∈ K, k ∈ infPts σ J) →
    (∀ ψ ∈ A, IsSm σ J ψ) → (∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A) →
    (∀ k ∈ K, ∀ ψ ∈ A, (fun x => ψ (x * k)) ∈ A) → Module.rank ℂ A ≤ Cardinal.aleph0 →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GAd σ J → ℂ)), StrictMono N → (∀ i, N i ≤ A) →
      (∀ i β, IsRealLine σ J β → ∀ ψ ∈ N i, lineDer β ψ ∈ N i) → (∀ i, ∀ k ∈ K, ∀ ψ ∈ N i, (fun x => ψ (x * k)) ∈ N i) →
      m ≤ L) →
    ∀ ψ₀ ∈ A, FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z ψ₀}) := by
  first | exact @GlobalTheory.ZFinAssembly.finiteDimensional_span_dop | exact GlobalTheory.ZFinAssembly.finiteDimensional_span_dop | (intros; apply GlobalTheory.ZFinAssembly.finiteDimensional_span_dop <;> assumption)
