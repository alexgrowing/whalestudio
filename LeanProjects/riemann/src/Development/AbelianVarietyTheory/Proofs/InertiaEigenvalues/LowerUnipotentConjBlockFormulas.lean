import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableHopfOrderSubgroupColength
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_conj_block_formulas : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  first | (exact @GlobalTheory.SchurExt.schur_mul_conjLowUni) | (exact GlobalTheory.SchurExt.schur_mul_conjLowUni) | (intros; apply GlobalTheory.SchurExt.schur_mul_conjLowUni  <;> assumption)
