import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverse
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse : ∀ (R : Type) [CommRing R] (m r : ℕ) (X Y : Matrix (Fin m) (Fin r) R) (X' Y' : Matrix (Fin r) (Fin m) R) (d e : Matrix (Fin r) (Fin r) R) (A B : Matrix (Fin m) (Fin m) R), X' * X = 0 → Y' * Y = 0 → X' * Y = 1 → Y' * X = 1 → d * e = 1 → e * d = 1 → A * X = X * d → A * Y = Y * e → A * (1 - X * Y' - Y * X') = 1 - X * Y' - Y * X' → A * B = 1 → Y' * B = e * Y' ∧ X' * B = d * X' ∧ (1 - X * Y' - Y * X') * B = 1 - X * Y' - Y * X' := by
  first | exact @GlobalTheory.torus_dual_frame_rows_eigen | exact GlobalTheory.torus_dual_frame_rows_eigen | (intros; apply GlobalTheory.torus_dual_frame_rows_eigen <;> assumption)
