import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTrivialAtInertPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_trivial_near_one : ∀ (D : D7) (N : ℕ), Even N → ∀ (χ : HeckeU D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((x : AE D) - 1)) → χ.f x = 1 := by
  first | exact @GlobalTheory.InertTrivial.character_trivial_at_inert | exact GlobalTheory.InertTrivial.character_trivial_at_inert | (intros; apply GlobalTheory.InertTrivial.character_trivial_at_inert <;> assumption)
