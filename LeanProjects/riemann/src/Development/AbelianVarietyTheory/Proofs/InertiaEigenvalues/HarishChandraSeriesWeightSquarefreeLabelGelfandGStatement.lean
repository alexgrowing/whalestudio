import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandG
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | exact GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev <;> assumption)
