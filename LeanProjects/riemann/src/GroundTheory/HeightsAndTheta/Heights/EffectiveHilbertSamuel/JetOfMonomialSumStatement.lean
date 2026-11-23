import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

def JetOfMonomialSum.Statement : Prop :=
  ∀ (n p : ℕ) (u : Fin p → (Fin n → ℂ) → ℂ) (h : (Fin p → ℕ) → (Fin n → ℂ) → ℂ)
    (z₀ : Fin n → ℂ) (a : ℕ),
    (∀ i, AnalyticAt ℂ (u i) z₀) → (∀ i, u i z₀ = 0) → (∀ α, AnalyticAt ℂ (h α) z₀) →
    (∀ k < a, iteratedFDeriv ℂ k
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ = 0) ∧
    iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ ∧
    ∀ w : Fin n → ℂ, iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀
        (fun _ => w) =
      (a.factorial : ℂ) * ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        (∏ i, (fderiv ℂ (u i) z₀ w) ^ α i) * h α z₀

end GroundTheory.Heights₂.Heights.EffectiveHS
