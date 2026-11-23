import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieOperatorEqSumColUnitaryActionBddDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colLieOperator_eq_sum_colUnitaryAction_bddDegree : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin n), ∃ (s : Finset (Matrix.unitaryGroup (Fin n) ℂ)) (c : Matrix.unitaryGroup (Fin n) ℂ → ℂ), ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ g ∈ s, c g • colSub m τ g P = colLie m τ k l P := by
  first | exact @GlobalTheory.DefLift.colLie_eq_sum_colSub | exact GlobalTheory.DefLift.colLie_eq_sum_colSub | (intros; apply GlobalTheory.DefLift.colLie_eq_sum_colSub <;> assumption)
