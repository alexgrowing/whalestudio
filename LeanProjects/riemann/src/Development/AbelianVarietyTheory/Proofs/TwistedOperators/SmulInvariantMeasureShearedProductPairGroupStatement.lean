import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N), κ.IsHaarMeasure → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → SMulInvariantMeasure (GlobalTheory.UnfoldNormal.pairGroup Γ N hN) (H × H) ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) := by
  first | exact @GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | exact GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | (intros; apply GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map <;> assumption)
