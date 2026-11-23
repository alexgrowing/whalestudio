import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemIdealOfFormalGroupCoboundaryOneCoeffMemA
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_coeff_cob1_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  first | exact @GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem | exact GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem | (intros; apply GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem <;> assumption)
