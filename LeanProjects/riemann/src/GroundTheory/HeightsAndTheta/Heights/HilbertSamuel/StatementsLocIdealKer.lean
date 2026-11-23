import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def LocIdealKer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (T : Submonoid (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓜 → IsMultiHomogIdeal P → (∀ t ∈ T, ∃ a : K → ℕ, IsMultiHomog t a) →
    ∀ w ∈ KH.locPart ι 𝓜 T d,
      (w ∈ locIdealPart 𝓜 T P d ↔
        IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
          (LocalizedModule.mkLinearMap T (M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M)))
          (P • ⊤ : Submodule (MRingOver S ι) M).mkQ w = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
