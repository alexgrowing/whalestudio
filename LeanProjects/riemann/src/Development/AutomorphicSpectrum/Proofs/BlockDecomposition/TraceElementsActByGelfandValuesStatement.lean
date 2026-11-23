import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_elements_act_by_gelfand_values : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E → (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) → ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | exact GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | (intros; apply GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli <;> assumption)
