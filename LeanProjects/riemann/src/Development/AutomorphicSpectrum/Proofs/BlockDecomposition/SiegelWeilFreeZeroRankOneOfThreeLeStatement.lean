import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilFree_zero_rank_one_of_three_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  first | exact @GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero | exact GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero | (intros; apply GlobalTheory.CompanionTheory.SW.OneZero.one_vector_zero <;> assumption)
