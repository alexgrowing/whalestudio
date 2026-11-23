import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def BlockResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) (P0' : Ideal (MRing ι)),
    A'.a = unitDeg d.k₀ → P0' ≤ mCoordIdeal d.y → IsSemipositiveRel P0' (mCoordIdeal d.y) A' →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Σ k, ι k) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
        (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) →
          σ n b (chartIdx A y) y = eval (fun p => c p.1 * blockPt d y p) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.A.h (fun p => c p.1 * blockPt d y p)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (A'.h (fun p => c p.1 * blockPt d y p))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => blockInterpPot d d.A A' t) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
