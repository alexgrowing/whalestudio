import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimitiveFormRemainder.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (N : ℕ) (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (n : σ → ℕ)
    (c : (i : σ) → Fin (n i) → (Fin d → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) → (∀ i j, AnalyticAt ℂ (c i j) (A w)) →
    (∀ i (T : ℂ), T ^ n i + ∑ j, c i j (A w) * T ^ (j : ℕ) = (T - w i) ^ n i) →
    AnalyticAt ℂ f w →
    ∃ (M : ℕ) (R : Polynomial ((Fin d → ℂ) → ℂ)), (∀ k, AnalyticAt ℂ (R.coeff k) (A w)) ∧
      ∀ᶠ z in 𝓝 w, (∀ i, z i ^ n i + ∑ j, c i j (A z) * z i ^ (j : ℕ) = 0) →
        (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
        δ (A z) ^ M * f z = R.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
