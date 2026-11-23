import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCardMatricesMulEqZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_left_kernel_matrices_eq_pow : ∀ (k : Type) [Field k] [Finite k] (m n j : ℕ) (A : Matrix (Fin n) (Fin n) k), Module.finrank k (LinearMap.range A.mulVecLin) + j = n → Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  first | exact @GlobalTheory.natCard_matrices_mul_eq_zero | exact GlobalTheory.natCard_matrices_mul_eq_zero | (intros; apply GlobalTheory.natCard_matrices_mul_eq_zero <;> assumption)
