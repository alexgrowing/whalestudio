import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

noncomputable section

def LineDegreeBundle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (F : HermLattice K n),
    F.lattice = (HermLattice.standard K n).lattice →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (E : HermitianBundle.{0} K')
      (φ : E.carrier ≃ₗ[𝓞 K'] (Fin n → 𝓞 K')),
      (∀ (σ' : K' →+* ℂ) (x y : E.carrier),
        (E.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] y) =
          star (fun j ↦ σ' (φ x j : K')) ⬝ᵥ
            (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (φ y j : K'))) →
      ∀ v : Fin n → 𝓞 K', v ≠ 0 →
        HermitianBundle.normDegree E ((satLine v).comap φ.toLinearMap) =
          F.lineDegree K' fun j ↦ (v j : K')

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
