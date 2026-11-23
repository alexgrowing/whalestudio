import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def HolomorphicImplicitGraph.Statement : Prop :=
  ∀ (n m : ℕ) (f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ) (y : EuclideanSpace ℂ (Fin n))
    (V : Set (EuclideanSpace ℂ (Fin n))),
    (∀ i, ContDiff ℂ 1 (f i)) → IsOpen V → y ∈ V → (∀ i, f i y = 0) →
    finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧
        graphPt e Φ '' Ω = {z | z ∈ U ∧ ∀ i, f i z = 0} ∧
        ∀ x ∈ Ω, LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          ⨅ i, LinearMap.ker (fderiv ℂ (f i) (graphPt e Φ x) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)

end

end GroundTheory.Heights₂.Heights
