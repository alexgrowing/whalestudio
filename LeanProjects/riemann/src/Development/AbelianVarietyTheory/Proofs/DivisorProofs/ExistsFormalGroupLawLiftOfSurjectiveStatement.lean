import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupLawLift_of_surjective : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  first | exact @GlobalTheory.LiftLaw.exists_isLift | exact GlobalTheory.LiftLaw.exists_isLift | (intros; apply GlobalTheory.LiftLaw.exists_isLift <;> assumption)
