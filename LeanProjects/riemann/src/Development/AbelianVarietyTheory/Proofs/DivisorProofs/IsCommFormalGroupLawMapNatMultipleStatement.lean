import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  first | exact @GlobalTheory.isLaw_map_nmul | exact GlobalTheory.isLaw_map_nmul | (intros; apply GlobalTheory.isLaw_map_nmul <;> assumption)
