import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsClosedUnitaryOfComplex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField MeasureTheory GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
open scoped ENNReal Matrix

section Weighted

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {N : ℕ}

def wNorm {V : HermSpace K N} (M : Majorant V) (c : InfinitePlace K → ℝ)
    (x : InfinitePlace K → Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ w, c w * (ReciprocityTheory.ChartRestriction.G.SA.hf (starRingEnd ℂ) (M.H w) (x w) (x w)).re)

def wCount {V : HermSpace K N} (M : Majorant V) (c : InfinitePlace K → ℝ) (VV : Set (Fin N → K))
    (t : ℝ) (g : RealPts V) : ℝ≥0∞ :=
  (({v | v ∈ VV ∧ wNorm M c (gAct g⁻¹ (realVec v)) < t} : Set (Fin N → K)).encard : ℝ≥0∞)

end Weighted

def WeightedScaling.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (c : InfinitePlace E → ℝ), (∀ w, 0 < c w) →
    ∀ (L : Submodule (𝓞 E) (Fin N → E)) (VV : Set (Fin N → E)),
    IsLattice L → VV ⊆ L → (∀ v ∈ VV, v ≠ 0 ∧ V.h v v = 0) →
    (∀ g : unitaryGroup V, g ∈ stab V L → ∀ v ∈ VV,
      ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ VV) →
    ∀ μ : Measure (RealPts V), μ.IsHaarMeasure →
    ∀ s : Set (RealPts V), IsFundamentalDomain (gammaInf V L) s μ →
    ∀ t : ℝ, (∀ θ : ℝ, 0 < θ → (∫⁻ g in s, wCount M c VV (θ * t) g ∂μ) =
        ENNReal.ofReal θ ^ (2 * fDeg E * (N - 1)) * ∫⁻ g in s, wCount M c VV t g ∂μ) ∧
      ((∃ C : ℕ, ∀ v ∈ VV, lineIndex L v ≤ C) → (∫⁻ g in s, wCount M c VV t g ∂μ) < ⊤)

end GroundTheory.Heights₂.Heights.NineStatements
