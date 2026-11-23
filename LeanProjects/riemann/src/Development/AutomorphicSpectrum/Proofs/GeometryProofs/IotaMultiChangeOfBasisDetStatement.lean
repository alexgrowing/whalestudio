import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_change_of_basis_det : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω), exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family <;> assumption)
