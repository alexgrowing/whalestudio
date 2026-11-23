import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspOnTranslCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_constant_term_vanishes_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (K : Subgroup (GAd σ J)), K ≤ infPts σ J →
      ∀ ψ : GAd σ J → ℂ, GlobalTheory.StdPar.IsCuspOn σ J X Y S K ψ → ∀ C : Subgroup (GAd σ J), IsCompact (C : Set (GAd σ J)) →
        (∀ y ∈ C, ofInf σ J (projInf σ J y) ∈ K) →
        (∀ y ∈ C, GlobalTheory.StdPar.IsCuspOn σ J X Y S K (fun g => ψ (g * y))) ∧
          FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ y ∈ C, f = fun g => ψ (g * y)}) := by
  first | exact @GlobalTheory.StdPar.isCuspOn_transl_compact | exact GlobalTheory.StdPar.isCuspOn_transl_compact | (intros; apply GlobalTheory.StdPar.isCuspOn_transl_compact <;> assumption)
