import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_ne_zero_of_lin_indep : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V), LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption)
