import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = ramificationIndex F L * e ∧ ramificationIndex F L = Nat.card ↥(lowerRamificationGroup F L 0) := by
  first | exact @GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | exact GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | (intros; apply GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext <;> assumption)
