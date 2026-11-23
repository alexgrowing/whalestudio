import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardGenericIrreducibleCharactersGLnLe
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_generic_irreducible_characters_GLn_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n → Set.ncard {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} ≤ g ^ n - g ^ (n - 1) := by
  first | exact @GlobalTheory.GLq.card_generic_irr_le | exact GlobalTheory.GLq.card_generic_irr_le | (intros; apply GlobalTheory.GLq.card_generic_irr_le <;> assumption)
