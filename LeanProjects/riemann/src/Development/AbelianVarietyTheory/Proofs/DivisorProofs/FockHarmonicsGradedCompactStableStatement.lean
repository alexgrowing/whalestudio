import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_graded_compactStable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)), (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) → (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧ KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧ KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧ ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  first | exact @GlobalTheory.FockAlg.harm_graded_stable | exact GlobalTheory.FockAlg.harm_graded_stable | (intros; apply GlobalTheory.FockAlg.harm_graded_stable <;> assumption)
