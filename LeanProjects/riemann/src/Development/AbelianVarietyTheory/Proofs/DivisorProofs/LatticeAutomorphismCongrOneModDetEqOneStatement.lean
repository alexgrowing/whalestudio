import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ), 3 ≤ m → (∀ x, CongMod m (k x) x) → LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  first | exact @GlobalTheory.Poinc.det_eq_one_of_congMod | exact GlobalTheory.Poinc.det_eq_one_of_congMod | (intros; apply GlobalTheory.Poinc.det_eq_one_of_congMod <;> assumption)
