import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_unique_of_irreducible : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), IsIrrRep π → ∀ f f', HasLab L π f → HasLab L π f' → f = f' := by
  first | exact @GlobalTheory.GLp.OneLabel.label_unique | exact GlobalTheory.GLp.OneLabel.label_unique | (intros; apply GlobalTheory.GLp.OneLabel.label_unique <;> assumption)
