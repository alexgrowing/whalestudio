import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbability
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  first | exact @GlobalTheory.IwConst.right_inv_eq_smul_left_inv | exact GlobalTheory.IwConst.right_inv_eq_smul_left_inv | (intros; apply GlobalTheory.IwConst.right_inv_eq_smul_left_inv <;> assumption)
