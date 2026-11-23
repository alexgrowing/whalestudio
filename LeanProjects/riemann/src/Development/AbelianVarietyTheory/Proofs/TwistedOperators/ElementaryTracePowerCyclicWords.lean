import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
open scoped InnerProductSpace

namespace GlobalTheory.TraceCycWord

theorem etr_succ_eq_sum_cycWord : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ),
    Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  intro A _ n E m
  rw [GlobalTheory.PhiEigenfun.sum_cycWord, Formalism.REAL.etr]
  exact Finset.sum_congr rfl fun c _ => GlobalTheory.PhiEigenfun.epow_eq E (m + 1) c c

end GlobalTheory.TraceCycWord
