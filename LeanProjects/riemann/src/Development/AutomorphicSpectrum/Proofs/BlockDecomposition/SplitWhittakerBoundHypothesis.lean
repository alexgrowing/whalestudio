import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitSmoothnessHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableModulusPowOnBoundedUnits
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitBound

open scoped Pointwise

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem det_diagonal_two (a : Fˣ) : ((dg2 a 1 : GL (Fin 2) F).val).det = a := by
  simp [dg2, Matrix.det_fin_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem nsg_one : nsg (F × F) (1 : F) = 1 := by
  unfold nsg
  rw [if_pos]
  exact ⟨1, by simp⟩

theorem wcS_diag (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (a : Fˣ) :
    WcS χ c₁ c₂ Ψ (dg2 a 1) = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) *
      ∫ u : Fˣ, Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F := by
  have hd : GeneralLinearGroup.det (dg2 a 1 : GL (Fin 2) F) = a := Units.ext (by
    simpa using det_diagonal_two a)
  have h00 : (dg2 a 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2]
  have h01 : (dg2 a 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
  have h10 : (dg2 a 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
  have h11 : (dg2 a 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
  unfold WcS
  rw [hd, det_diagonal_two, h00, h01, h10, h11]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have ha : (a : F) / a = 1 := div_self a.ne_zero
  simp only [rW, ha, zero_div, if_true, nsg_one]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.SplitBound
