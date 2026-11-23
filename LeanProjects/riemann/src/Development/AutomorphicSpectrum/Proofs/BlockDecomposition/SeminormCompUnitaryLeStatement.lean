import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeminormCompUnitaryLe
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seminorm_comp_unitary_le : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : Matrix (Fin 2) (Fin 2) ℂ, κ * κᴴ = 1 →
    ∀ f : SchwartzMap (Fin 2 → ℂ) ℂ, ∃ f' : SchwartzMap (Fin 2 → ℂ) ℂ,
      (∀ v, f' v = f (Matrix.vecMul v κ)) ∧ pS N f' ≤ C * pS N f := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | exact GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded | (intros; apply GlobalTheory.CompanionTheory.UnitaryCompSchwartz.comp_unitary_bounded <;> assumption)
