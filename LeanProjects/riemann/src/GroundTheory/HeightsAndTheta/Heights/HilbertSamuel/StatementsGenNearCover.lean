import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearCover.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (V : Ideal (MRingOver S ι)) (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (deg : ℕ → K → ℤ),
    IsNoetherianRing S → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    (∀ P : Ideal (MRingOver S ι), IsClosedMultiPt P → V ≤ P →
      ∃ (f : MRingOver S ι) (δ : K → ℕ) (c₀ : ℕ), IsMultiHomog f δ ∧ f ∉ P ∧
        ∀ c : ℕ, c₀ ≤ c → GenNear S ι 𝓜 (deg c) f δ) →
    ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → GeneratedMod S ι 𝓜 (deg c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
