import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterEqZeroOfIsNilpotent
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ x : R, IsNilpotent x → T x = 0 := by
  first | exact @GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | exact GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent <;> assumption)
