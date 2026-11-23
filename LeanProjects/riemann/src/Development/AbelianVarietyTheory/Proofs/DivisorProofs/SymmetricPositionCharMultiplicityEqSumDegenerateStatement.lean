import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerate
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  first | exact @GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | exact GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | (intros; apply GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum <;> assumption)
