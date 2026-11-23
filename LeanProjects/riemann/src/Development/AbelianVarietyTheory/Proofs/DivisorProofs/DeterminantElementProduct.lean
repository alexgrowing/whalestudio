import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_mul {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ r r' : R) (n n' : ℕ)
    (c c' : C) (h : Lead f ξ r n c) (h' : Lead f ξ r' n' c') :
    Lead f ξ (r * r') (n + n') (c * c') := by
  obtain ⟨s, t, hs, hr, ht⟩ := h
  obtain ⟨s', t', hs', hr', ht'⟩ := h'
  refine ⟨s * s', t * t', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs hs'
  · calc s * s' * (r * r') = (s * r) * (s' * r') := by ring
      _ = ξ ^ (n + n') * (t * t') := by rw [hr, hr', pow_add]; ring
  · rw [map_mul, map_mul, ht, ht']; ring

theorem detData_mul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  intro p _ O _ _ _ C _ _ ε Λ _ _ ψ N N' Δ Δ' a a' c c' h1 h2 h3 h4
  obtain ⟨hd, g, hg, hgd⟩ := h1
  obtain ⟨hd', g', hg', hgd'⟩ := h2
  refine ⟨⟨?_, g * g', ?_, ?_⟩, ?_⟩
  · rw [pow_add]; exact mul_dvd_mul hd hd'
  · rw [map_mul]
    calc Δ * Δ' = (g * ψ Δ) * (g' * ψ Δ') := by rw [← hg, ← hg']
      _ = g * g' * (ψ Δ * ψ Δ') := by ring
  · rw [pow_add]; exact mul_dvd_mul hgd hgd'
  · intro σ f hf
    obtain ⟨ha, hc, hl⟩ := h3 σ f hf
    obtain ⟨ha', hc', hl'⟩ := h4 σ f hf
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.mul_apply]; exact mul_ne_zero hc hc'
    · simpa only [Pi.add_apply, Pi.mul_apply] using lead_mul _ _ _ _ _ _ _ _ hl hl'

end GlobalTheory.DetInv
