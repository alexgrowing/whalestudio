import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  first | exact @GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | exact GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | (intros; apply GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl <;> assumption)
