import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

def LocalLatticeIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (v : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (g : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    IsLocalLattice v A → (B : Set (v.adicCompletion K ⊗[K] V)) = g '' A → B ≤ A →
      (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ‖LinearMap.det
          ((g : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖⁻¹

section Witness

variable (K : Type u) [Field K] [NumberField K]

theorem LocalLatticeIndex.witness (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalLattice v (localLattice v (FullLattice.standard K 2).carrier) ∧
      (localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier :
          Set (v.adicCompletion K ⊗[K] (Fin 2 → K))) =
        localSmul v (two_ne_zero (α := 𝓞 K)) '' localLattice v (FullLattice.standard K 2).carrier ∧
      localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
        localLattice v (FullLattice.standard K 2).carrier :=
  ⟨localLattice_isLocalLattice v _, localLattice_smulSub v _ _,
    Submodule.span_mono (Set.image_mono (smulSub_le _ _))⟩

example := LocalLatticeIndex.witness ℚ (Classical.choice nonempty_heightOneSpectrum)
example := LocalLatticeIndex.witness GaussianField (Classical.choice nonempty_heightOneSpectrum)

end Witness

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
