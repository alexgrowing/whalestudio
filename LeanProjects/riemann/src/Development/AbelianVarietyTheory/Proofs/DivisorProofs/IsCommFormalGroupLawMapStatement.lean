import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map : ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  first | exact @GlobalTheory.Katz.isLaw_map | exact GlobalTheory.Katz.isLaw_map | (intros; apply GlobalTheory.Katz.isLaw_map <;> assumption)
