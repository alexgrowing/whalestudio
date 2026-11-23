import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardMonicNatDegreeCoeffZeroNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_monic_natDegree_coeff_zero_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  first | exact @GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero | exact GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero | (intros; apply GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero <;> assumption)
