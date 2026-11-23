import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSheetSimpleNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def PtsGenericCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ d : ℕ, (∀ y, (fibre P Ψ y).encard ≤ d) ∧
        volume {y : Fin e → ℂ | ¬ ((fibre P Ψ y).encard = d ∧
          ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ)} = 0

end GroundTheory.Heights₂.Heights
