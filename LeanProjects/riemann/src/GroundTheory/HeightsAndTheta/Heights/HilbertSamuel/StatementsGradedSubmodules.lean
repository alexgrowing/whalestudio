import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GradedSubmodules.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    KH.IsMGraded S ι 𝓜 →
    IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M) ∧
      ∀ P : Ideal (MRingOver S ι), IsMultiHomogIdeal P →
        KH.IsMGraded S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) ∧
          KH.IsMGraded S ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
