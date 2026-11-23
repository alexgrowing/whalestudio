import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntModuleFiniteOfSeparatedOfFiniteQuotientA
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_module_finite_of_separated : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X], Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))) → (∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) → Module.Finite ℤ_[l] X := by
  first | exact @GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | exact GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | (intros; apply GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient <;> assumption)
