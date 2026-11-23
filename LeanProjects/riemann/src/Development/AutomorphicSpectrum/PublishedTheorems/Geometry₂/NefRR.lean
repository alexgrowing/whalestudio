import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric

namespace GlobalTheory.CompanionTheory.Ar.Pub

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

def NefRR : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a →
      (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))) ∧
      Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ) /
        (τ : ℝ) ^ D) atTop (𝓝 (genDeg (mCoordIdeal y) D a : ℝ))

end GlobalTheory.CompanionTheory.Ar.Pub
