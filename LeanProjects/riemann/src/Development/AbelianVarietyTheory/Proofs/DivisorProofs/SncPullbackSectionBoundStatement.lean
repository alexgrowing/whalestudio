import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncPullbackSectionBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_pullback_section_bound : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y)
    (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y) (m₀ : Fin r → ℕ),
    IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) m₀ W →
    ∀ [MeasurableSpace Y] [BorelSpace Y] (Φ : Fin n → LocPot Y), (∀ i, IsPotential B (Φ i)) →
    (∀ i, IsPsh B (Φ i)) →
    ∫⁻ y, absLogNorm L s (μ y) ∂maMeasure B Φ ≤
      ENNReal.ofReal (mInt B Φ (fun y => -logNormSec L s (μ y))) := by
  first | exact @GlobalTheory.LogNormPullbackBound.lintegral_absLogNorm_le | exact GlobalTheory.LogNormPullbackBound.lintegral_absLogNorm_le | (intros; apply GlobalTheory.LogNormPullbackBound.lintegral_absLogNorm_le <;> assumption)
