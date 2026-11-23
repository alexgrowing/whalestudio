import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

def LiftBirationalNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (b a₀ : ℕ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.NefOnF I (KH.genIdeal y) α →
    1 ≤ b → 1 ≤ a₀ →
    ∃ q t₀ : ℕ, 1 ≤ q ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • (b • α + fun _ => (a₀ : ℤ))) 1) ∧
        Birational (fun p : Σ _ : Unit, Fin r => x' p.2)

noncomputable abbrev ptFamily : IFamily ℚ PtIdx := fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L

end GroundTheory.Heights₂.Heights.HilbertSamuel
