import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_pullback_holomorphic : ∀ (d n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (L : LocPot X) (s : X → X → ℂ),
    IsSection A L s → IsSection B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) := by
  first | exact @GlobalTheory.isSection_pullback_holoMap | exact GlobalTheory.isSection_pullback_holoMap | (intros; apply GlobalTheory.isSection_pullback_holoMap <;> assumption)
