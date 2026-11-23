import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockImageChi.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d₀.k₀) ℤ)
    (N : Matrix (ι d₀.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
    IsBlockImage d₀.y d₀.k₀ M N d'.x →
    (∀ z ∈ mcPts (mCoordIdeal d₀.y), d₀.A.h z = d'.m.ρ (blockMapC d₀.k₀ M z)) →
    (∀ g : (Ix (Fin r) → ℂ) → ℂ, ContinuousOn g {0}ᶜ → (∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) →
      ∫ a, g (resPt d' a) ∂d'.dV = ∫ a, g (blockMapC d₀.k₀ M (blockPt d₀ a)) ∂d₀.dV) →
    ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
