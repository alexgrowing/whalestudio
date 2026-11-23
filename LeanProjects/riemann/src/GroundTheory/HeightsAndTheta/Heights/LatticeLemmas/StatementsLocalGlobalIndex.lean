import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

def LocalGlobalIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M₁ M₂ : FullLattice K V),
    M₂.carrier ≤ M₁.carrier →
      (Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) : ℝ) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((localLattice v M₂.carrier).toAddSubgroup.relIndex
          (localLattice v M₁.carrier).toAddSubgroup : ℝ)

section Witness

variable (K : Type u) [Field K] [NumberField K]

theorem LocalGlobalIndex.witness :
    (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
      (FullLattice.standard K 2).carrier :=
  smulSub_le _ _

example := LocalGlobalIndex.witness ℚ
example := LocalGlobalIndex.witness GaussianField

end Witness

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
