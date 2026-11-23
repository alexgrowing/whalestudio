import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsStrictlySemistableIff
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) → GlobalTheory.SSG.ChartAt ϖ p x := by
  first | (exact @GlobalTheory.SSG.chartAt_of_smooth) | (exact GlobalTheory.SSG.chartAt_of_smooth) | (intros; apply GlobalTheory.SSG.chartAt_of_smooth  <;> assumption)
