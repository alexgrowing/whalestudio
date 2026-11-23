import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSectionBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_potential_section_bound : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    chartSumInt B ((poincarePot α Λ σ c).pullback μ hμ.1) (μ ⁻¹' boundary σ)ᶜ
      (fun y => absLogNorm L s (μ y)) < ∞ := by
  first | exact @GlobalTheory.LogResInt.onResolution | exact GlobalTheory.LogResInt.onResolution | (intros; apply GlobalTheory.LogResInt.onResolution <;> assumption)
