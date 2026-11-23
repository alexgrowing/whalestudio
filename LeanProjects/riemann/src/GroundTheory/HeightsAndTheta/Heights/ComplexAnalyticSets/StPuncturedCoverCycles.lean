import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def PuncturedCoverCycles.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (c : Fin (e + 1) → ℂ) (r : ℝ)
    (X : Set (Fin n → ℂ)),
    0 < r → c 0 = 0 →
    (∀ x ∈ X, dist (A *ᵥ x) c < r ∧ (A *ᵥ x) 0 ≠ 0) →
    (∀ y : Fin (e + 1) → ℂ, dist y c < r → y 0 ≠ 0 → {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧
      (∀ b, DifferentiableOn ℂ (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b, ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ψ b t ∈ X ∧ A *ᵥ ψ b t = Function.update t 0 (t 0 ^ ord b)) ∧
      (∀ b, Set.InjOn (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b b', b ≠ b' → ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ∀ t' ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t ≠ ψ b' t') ∧
      (∀ x ∈ X, dist (A *ᵥ x) c < δ ^ N →
        ∃ b, ∃ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t = x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
