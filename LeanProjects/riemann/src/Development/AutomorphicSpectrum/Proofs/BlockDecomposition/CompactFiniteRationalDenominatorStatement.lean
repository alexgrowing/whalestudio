import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteRationalDenominator
import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finite_rational_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.bounded_denominators | exact GlobalTheory.CompanionTheory.CFin.bounded_denominators | (intros; apply GlobalTheory.CompanionTheory.CFin.bounded_denominators <;> assumption)
