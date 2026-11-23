import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockVeronese.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (N : ℕ) (v : Fin N → Ω),
      AddSubgroup.closure (Set.range v) = chartLat y a m ∧
      KH.GeneratesOn y (fun k => (m : ℤ) * a k) v ∧
      ∀ n : ℕ, 1 ≤ n → chartLat y a (m * n) = secM (addBlock y v) (blockDeg (none : Option K) n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
