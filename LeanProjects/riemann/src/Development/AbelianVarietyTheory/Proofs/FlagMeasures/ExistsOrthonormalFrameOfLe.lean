import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicOrthogonalDecomposition

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

theorem exists_orthonormal_frame_of_le : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ S : Submodule ℂ (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), S ≤ B.I.HomS B.σs B.μf B.fund B.R → FiniteDimensional ℂ S → ∃ T : Fin (Module.finrank ℂ S) → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ S) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ ∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0 := by
  intro B d hd S hle hfin
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨-, -, hR, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs
      map_one' := hU.1
      map_mul' := hU.2.1 }
  obtain ⟨T, h1, h2, h3, -⟩ := exists_frame S (B.tens B.w) fun T hT T' hT' u u' =>
    inner_intertwiners σ hU.2.2.1 hirr (fun g => B.R (g, 1)) (fun g => hR _) _ hw T T' (hle hT) (hle hT') u u'
  exact ⟨T, h1, h2, h3⟩

end GlobalTheory.IntertwinerFrame
