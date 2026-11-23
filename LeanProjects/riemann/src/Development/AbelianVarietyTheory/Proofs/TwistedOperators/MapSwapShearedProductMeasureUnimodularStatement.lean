import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_swap_sheared_product_measure_unimodular : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H), IsClosed (N : Set H) → ∀ (κ : Measure N), κ.IsHaarMeasure → κ.map (fun n => n⁻¹) = κ → ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  first | exact @GlobalTheory.UnfoldNormal.map_swap_map_shear | exact GlobalTheory.UnfoldNormal.map_swap_map_shear | (intros; apply GlobalTheory.UnfoldNormal.map_swap_map_shear <;> assumption)
