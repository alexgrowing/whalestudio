import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnHighestRowIntertwinersProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnHighest_rowIntertwiners_proportional : ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π → ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 → (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) → (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) → (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) → ∃ r : ℂ, Ψ = r • Φ := by
  first | exact @GlobalTheory.DefLift.colHighest_intertwiner_proportional | exact GlobalTheory.DefLift.colHighest_intertwiner_proportional | (intros; apply GlobalTheory.DefLift.colHighest_intertwiner_proportional <;> assumption)
