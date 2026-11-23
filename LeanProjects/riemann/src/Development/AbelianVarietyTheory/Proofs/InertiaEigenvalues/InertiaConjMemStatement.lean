import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_inertia_of_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  first | exact @GlobalTheory.InertiaConj.inertia_conj_mem | exact GlobalTheory.InertiaConj.inertia_conj_mem | (intros; apply GlobalTheory.InertiaConj.inertia_conj_mem <;> assumption)
