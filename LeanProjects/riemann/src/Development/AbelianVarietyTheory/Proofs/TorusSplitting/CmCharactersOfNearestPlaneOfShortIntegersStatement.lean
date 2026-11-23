import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CmCharactersOfNearestPlaneOfShortIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.cmCharacters_of_nearestPlane_of_short_integers : Ext.NearestPlane → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧ ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E)) → CharStatement := by
  first | exact @GlobalTheory.characters_of_nearestPlane_of_short_integers | exact GlobalTheory.characters_of_nearestPlane_of_short_integers | (intros; apply GlobalTheory.characters_of_nearestPlane_of_short_integers <;> assumption)
