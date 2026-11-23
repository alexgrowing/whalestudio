import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMul
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_scalar_mul : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quot_smul_range_finite_free | exact GlobalTheory.length_quot_smul_range_finite_free | (intros; apply GlobalTheory.length_quot_smul_range_finite_free <;> assumption)
