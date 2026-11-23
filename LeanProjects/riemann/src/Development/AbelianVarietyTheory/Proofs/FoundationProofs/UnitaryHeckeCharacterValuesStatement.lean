import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharacter_values : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (x : (AE D)ˣ), Mod1All ((χ.f x : ℂˣ) : ℂ) ∧ (IntU D x → ∃ m : ℕ, 0 < m ∧ χ.f x ^ m = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (∃ y : (AE D)ˣ, IntU D y ∧ ZeroAt D p (((x * y : (AE D)ˣ) : AE D) - 1)) → ‖lamC lam ((χ.f x : ℂˣ) : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.HeckeVal.hecke_values | exact GlobalTheory.HeckeVal.hecke_values | (intros; apply GlobalTheory.HeckeVal.hecke_values <;> assumption)
