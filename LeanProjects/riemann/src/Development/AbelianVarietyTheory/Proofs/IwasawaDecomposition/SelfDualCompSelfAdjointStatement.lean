import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualCompSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_sqrt_smul_comp_of_invariant : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  first | exact @GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | exact GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | (intros; apply GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint <;> assumption)
