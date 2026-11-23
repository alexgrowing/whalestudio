import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

def normSq (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

def complementOf (De : MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | MvPolynomial.eval x De ≠ 0}

def HolomorphicAlong (z : MS → (Fin n → ℂ)) (u : MS → ℂ) : Prop :=
  ∀ p : MS, ∃ e : OpenPartialHomeomorph MS (Fin n → ℂ),
    p ∈ e.source ∧ (∀ q ∈ e.source, z q = e q) ∧ AnalyticOnNhd ℂ (u ∘ e.symm) e.target

def OrderGT (z : MS → (Fin n → ℂ)) (u : MS → ℂ) (p : MS) (m : ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ q in 𝓝 p, ‖u q‖ ≤ C * Real.sqrt (normSq (z q - z p)) ^ (m + 1)

def IsCoveringOfDegree (z : MS → (Fin n → ℂ)) (B : Set (Fin n → ℂ)) (δ : ℕ) : Prop :=
  ∃ h : ∀ p, z p ∈ B, IsCoveringMap (Set.codRestrict z B h) ∧
    ∀ x ∈ B, (z ⁻¹' {x}).encard = δ

def NormLemma.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (u : MS → ℂ) (C : ℝ) (m : ℕ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z u →
    (∀ p, ‖u p‖ ≤ C * (1 + normSq (z p)) ^ ((m : ℝ) / 2)) →
    (∀ p, z p = 0 → OrderGT z u p m) →
    u = 0

def ShareCore.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (f θ τ : MS → ℂ) (C : ℝ) (e a : ℕ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z f → HolomorphicAlong z θ → HolomorphicAlong z τ →
    θ ≠ 0 → τ ≠ 0 →
    (∀ p, ‖f p * θ p * τ p ^ a‖ ≤ C * (1 + normSq (z p)) ^ ((e : ℝ) / 2)) →
    (∀ p, z p = 0 → OrderGT z f p e) →
    f = 0

def ShareNumbers.Statement : Prop :=
  ∀ D N T : ℕ, 6 ≤ D → 2 * N ≤ D → 11 * D ^ 2 ≤ T →
    8 * ((T + 2 * D + 4 + N + 15) / 16) ≤ T + 8 ∧
    (T + 2 * D + 4 + N) + D + 1 - T = 3 * D + 5 + N ∧
    2 * (3 * D + 5 + N) ≤ 9 * D

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.EffectiveHS
