import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingPieces.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (c : (F →+* ℂ) → ℝ)
    (w : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → w =ᶠ[𝓝 z] fun _ => c sg) →
    ptsIntegral (mCoordIdeal y) (pot L) w =
      (∑ sg, c sg) / Fintype.card (F →+* ℂ) * ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
