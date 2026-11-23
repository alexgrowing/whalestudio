import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProduct
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧ (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧ ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ = ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  first | exact @GlobalTheory.CompactHowe.Minors.exists_highestWeight | exact GlobalTheory.CompactHowe.Minors.exists_highestWeight | (intros; apply GlobalTheory.CompactHowe.Minors.exists_highestWeight <;> assumption)
