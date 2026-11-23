import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : Type) [Field k] (r : O →+* k), Function.Surjective r → ∀ (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ m : GL (Fin n) K, (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹ ∧ ψ (edgeVal ρ κ a (bc r x')) = ψ (edgeVal ρ κ a (bc r x))) → (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m⁻¹ * bc O.subtype x * m) → IsScal O m := by
  first | exact @GlobalTheory.ScalInt.isScal_of_normalises | exact GlobalTheory.ScalInt.isScal_of_normalises | (intros; apply GlobalTheory.ScalInt.isScal_of_normalises <;> assumption)
