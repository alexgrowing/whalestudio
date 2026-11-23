import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧ ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b → ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  first | (exact @GlobalTheory.W1.Base.forms_baseChange) | (exact GlobalTheory.W1.Base.forms_baseChange) | (intros; apply GlobalTheory.W1.Base.forms_baseChange  <;> assumption)
