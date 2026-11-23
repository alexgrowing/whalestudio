import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatePointsSmoothFiniteSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separate_points_smooth_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ Kc : Subgroup (GAd σ J), IsCompact (Kc : Set (GAd σ J)) → ∀ x ∈ Kc, ∀ y ∈ Kc, projFin σ J x ≠ projFin σ J y →
      ∃ V : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ V ∧
        (∀ w ∈ V, Continuous w ∧ GlobalTheory.UAut.IsSm σ J w ∧
          (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ u ∈ U, u ∈ finPts σ J → ∀ g, w (g * u) = w g) ∧
          ∀ k ∈ Kc, (fun g => w (k * g)) ∈ V ∧ (fun g => w (g * k)) ∈ V) ∧ ∃ f ∈ V, f x ≠ f y := by
  first | exact @GlobalTheory.FinSep.exists_finDim_separating | exact GlobalTheory.FinSep.exists_finDim_separating | (intros; apply GlobalTheory.FinSep.exists_finDim_separating <;> assumption)
