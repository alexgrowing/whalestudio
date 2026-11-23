import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvections
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  first | exact @GlobalTheory.UTrans.TvKill.char_tvGen | exact GlobalTheory.UTrans.TvKill.char_tvGen | (intros; apply GlobalTheory.UTrans.TvKill.char_tvGen <;> assumption)
