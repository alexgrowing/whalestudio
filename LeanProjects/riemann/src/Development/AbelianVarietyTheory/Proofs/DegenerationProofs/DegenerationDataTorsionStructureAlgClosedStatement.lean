import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_torsion_structure_algClosed : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (n g : ℕ), (n : C) ≠ 0 → N.Tors n g → ∀ j : ℕ, (∀ b : N.A, ∃ γ : N.Gt, γ.b = b) ∧ (∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ) ∧ (∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) ∧ Nonempty ((powMonoidHom (n ^ j) : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (2 * g + Module.finrank ℤ N.X) → ZMod (n ^ j))) ∧ (∀ p : N.QT (n ^ j), (∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT (n ^ j), N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1) ∧ ∀ p : N.QT (n ^ j), (∀ p', N.wp p p' = 1) → N.QEq p 1 := by
  first | exact @GlobalTheory.Ex.QStr.qStructure | exact GlobalTheory.Ex.QStr.qStructure | (intros; apply GlobalTheory.Ex.QStr.qStructure <;> assumption)
