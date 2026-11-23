import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NefAmpleFibre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (b a ℓ : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → NefOnFibres (mCoordIdeal y) α → 1 ≤ b → 1 ≤ a → ℓ.Prime →
    KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) ((b : ℤ) • α + fun _ => (a : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
