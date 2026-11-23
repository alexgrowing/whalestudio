import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_one_sub_frobenius_surjective : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.OneSubPhiOnto := by
  first | exact @GlobalTheory.MemLoc.one_sub_phi_onto | exact GlobalTheory.MemLoc.one_sub_phi_onto | (intros; apply GlobalTheory.MemLoc.one_sub_phi_onto <;> assumption)
