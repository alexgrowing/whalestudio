import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M), (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  first | exact @GlobalTheory.projective_dvd_of_forall_dual_dvd | exact GlobalTheory.projective_dvd_of_forall_dual_dvd | (intros; apply GlobalTheory.projective_dvd_of_forall_dual_dvd <;> assumption)
