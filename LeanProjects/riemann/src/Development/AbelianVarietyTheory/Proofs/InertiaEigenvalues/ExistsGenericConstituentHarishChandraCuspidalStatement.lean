import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidal
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) → ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | exact GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | (intros; apply GlobalTheory.GLq.GenericConstituent.exists_generic_constituent <;> assumption)
