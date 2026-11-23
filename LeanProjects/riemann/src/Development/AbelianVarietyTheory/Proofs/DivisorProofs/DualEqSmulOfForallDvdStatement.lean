import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_eq_smul_of_forall_dvd' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) → ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  first | exact @GlobalTheory.dual_eq_smul_of_forall_dvd | exact GlobalTheory.dual_eq_smul_of_forall_dvd | (intros; apply GlobalTheory.dual_eq_smul_of_forall_dvd <;> assumption)
