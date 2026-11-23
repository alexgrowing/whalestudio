import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

theorem mul_mem_schwartzA : ∀ (D : D7) (θ : InfFam D) (m n : ℕ) (q : (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ), q.HasTemperateGrowth → ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → (fun x => q (fun τ i j => compAt θ τ x i j) * φ x) ∈ schwartzA θ m n := by
  intro D θ m n q hq φ hφ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine Submodule.subset_span ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hq f, g, hg, ?_⟩
    funext x
    simp [mul_assoc]
    exact mul_left_comm _ _ _
  | zero =>
    convert (schwartzA θ m n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    have := (schwartzA θ m n).add_mem h₁ h₂
    convert this using 1
    funext x
    simp [mul_add]
  | smul c Φ _ h =>
    have := (schwartzA θ m n).smul_mem c h
    convert this using 1
    funext x
    simp [mul_left_comm]

end GlobalTheory.CompanionTheory.WSum
end
