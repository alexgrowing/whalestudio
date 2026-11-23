import Mathlib

open Finset Classical

noncomputable section

namespace Formalism.NG

def blockSum {Ir ι : Type*} (tw : ℤ → Ir → Ir) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) :
    Multiset Ir :=
  ∑ i ∈ I, ∑ k ∈ range (dd i), (rp i).map (tw ((dd i : ℤ) - 1 - 2 * k))

def StatLowestInZ : Prop :=
  ∀ (Ir Irb : Type*) (rk : Ir → ℕ) (wt : Ir → ℤ) (tw : ℤ → Ir → Ir) (red : Ir → Multiset Irb)
    (rkb : Irb → ℕ),
    (∀ σ, 1 ≤ rk σ) → (∀ τ, 1 ≤ rkb τ) → (∀ σ, ((red σ).map rkb).sum = rk σ) →
    (∀ σ, tw 0 σ = σ) → (∀ a b σ, tw (a + b) σ = tw a (tw b σ)) →
    (∀ b σ, wt (tw b σ) = wt σ - b) → (∀ b σ, rk (tw b σ) = rk σ) →
    (∀ b σ, (red (tw b σ)).map rkb = (red σ).map rkb) →
    ∀ (ι : Type*) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) (w₀ : ℤ) (t : ℕ),
      2 ≤ t → (∀ i ∈ I, 1 ≤ dd i) → (∀ i ∈ I, ∀ σ ∈ rp i, wt σ = w₀) →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => 1 < rkb τ)) = 1 →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => rkb τ = 1)) = t →
    ∀ χ₁ : Ir, rk χ₁ = 1 → wt χ₁ = w₀ - ((t : ℤ) - 1) → χ₁ ∈ blockSum tw I rp dd →
      ∃ i ∈ I, dd i = t ∧ rp i = {tw (-((t : ℤ) - 1)) χ₁}

end Formalism.NG
