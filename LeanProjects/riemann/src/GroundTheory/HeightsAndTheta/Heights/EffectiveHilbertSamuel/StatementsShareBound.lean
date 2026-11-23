import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

def shareExp (e : ℕ) : ℕ := (e + 15) / 16

def ShareBound.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (e : ℕ) (f τ w₀ : MS → ℂ) (s : Fin n → MS → ℂ) (hF hθ hτ hW wn rh : MS → ℝ)
    (κ Cf Cτ cw CompactFixesLatticeTheory K : ℝ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z f → HolomorphicAlong z τ → HolomorphicAlong z w₀ →
    (∀ p, w₀ p ≠ 0) → (∀ p i, s i p = z p i * w₀ p) →
    (∀ p, 0 < hF p) → (∀ p, 0 < hθ p) → (∀ p, 0 < hτ p) → (∀ p, 0 < hW p) → 0 < κ →
    (∀ p, hF p * hθ p * hτ p ^ shareExp e = κ * hW p ^ e) →
    (∀ p, ‖f p‖ * hF p ≤ Cf) →
    (∃ (θ : MS → ℂ) (Cθ : ℝ), HolomorphicAlong z θ ∧ θ ≠ 0 ∧ ∀ p, ‖θ p‖ * hθ p ≤ Cθ) →
    τ ≠ 0 →
    (∀ p, ‖τ p‖ * hτ p ≤ Cτ * Real.exp (-(4 * rh p))) →
    0 < cw → (∀ p, 0 ≤ wn p) → (∀ p, cw * Real.exp (-(rh p / 2)) ≤ wn p ^ 2) →
    (∀ p, -K ≤ rh p) →
    (∀ p, wn p ≤ CompactFixesLatticeTheory * (hW p * Real.sqrt (‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2))) →
    f = 0 ∨ ∃ p, z p = 0 ∧ ¬ OrderGT z f p e

section Inhabitant

end Inhabitant

end

end GroundTheory.Heights₂.Heights.EffectiveHS
