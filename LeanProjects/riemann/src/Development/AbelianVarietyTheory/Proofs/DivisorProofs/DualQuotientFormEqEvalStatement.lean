import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEval
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_dual_quotient_form_eq_eval : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I), ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  first | exact @GlobalTheory.dual_quotient_form_eq_eval | exact GlobalTheory.dual_quotient_form_eq_eval | (intros; apply GlobalTheory.dual_quotient_form_eq_eval <;> assumption)
