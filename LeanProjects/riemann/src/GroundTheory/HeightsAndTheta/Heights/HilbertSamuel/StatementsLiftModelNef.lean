import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftBirationalNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

def LiftModelNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (b a₀ : ℕ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.NefOnF I (KH.genIdeal y) α →
    1 ≤ b → 1 ≤ a₀ →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (b • α + fun _ => (a₀ : ℤ))) →
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat y (a • (b • α + fun _ => (a₀ : ℤ))) 1) ∧
        KH.GeneratesOn y (a • (b • α + fun _ => (a₀ : ℤ))) x' ∧ Birational (fun p : Σ _ : Unit, ι' => x' p.2)

end GroundTheory.Heights₂.Heights.HilbertSamuel
