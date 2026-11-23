import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  first | exact @GlobalTheory.Katz.Chart.isLaw_of_isLawOf | exact GlobalTheory.Katz.Chart.isLaw_of_isLawOf | (intros; apply GlobalTheory.Katz.Chart.isLaw_of_isLawOf <;> assumption)
