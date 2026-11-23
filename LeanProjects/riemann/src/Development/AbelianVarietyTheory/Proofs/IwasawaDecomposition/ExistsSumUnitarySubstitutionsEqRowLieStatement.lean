import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m), ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ), ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  first | exact @GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | exact GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | (intros; apply GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie <;> assumption)
