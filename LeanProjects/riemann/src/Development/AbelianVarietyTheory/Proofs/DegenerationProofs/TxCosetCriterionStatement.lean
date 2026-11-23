import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tx_coset_norm_one_and_ne_zero : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  first | exact @GlobalTheory.tx_coset_criterion | exact GlobalTheory.tx_coset_criterion | (intros; apply GlobalTheory.tx_coset_criterion <;> assumption)
