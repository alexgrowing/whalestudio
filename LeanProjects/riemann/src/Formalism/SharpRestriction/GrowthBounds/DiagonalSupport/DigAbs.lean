import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

def DigAbs (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (σ : Type) [Fintype σ] (g rho : σ → ℕ), (∀ v, rho v < p ^ g v) →
    (∀ be : σ →₀ ℕ, (∏ v, gamR (p ^ g v) (rho v) (be v)) ≠ 0 ∧
      padicValRat p (∏ v, gamR (p ^ g v) (rho v) (be v)) = 0) ∧
    ∀ (inv : Bool) (c : ℕ), ∃ lam : (σ →₀ ℕ) →₀ O, (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 4 * c) ∧
      ∀ be : σ →₀ ℕ,
        geQ (vK p ((if inv then (((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O))⁻¹
            else ((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O)) - binomCombF (K := KK O) lam be)) (c : ℝ)

end Formalism.MainNotions.Proposition5Numerics
