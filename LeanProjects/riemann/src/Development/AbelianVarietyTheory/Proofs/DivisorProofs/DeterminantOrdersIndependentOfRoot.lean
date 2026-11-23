import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open WittVector

namespace GlobalTheory

theorem detData_indep_eps : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε ε' Λ _ _ ψ N Δ a c hxi hmu hD hH
  obtain ⟨u, hu⟩ := hxi
  obtain ⟨w, hw⟩ := hmu
  have key : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x : Ainf p O,
      f (inA x) = fontaineTheta O p x := by
    intro σ f hf x
    have := hf x 1
    rw [map_one, mul_one] at this
    rw [← this]
    rfl
  have hxd : (inA (xi ε) : RL p O Λ) ^ N ∣ (inA (xi ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(u : Ainf p O), hu.symm⟩) N
  have hmd : (inA (mu ε) : RL p O Λ) ^ N ∣ (inA (mu ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(w : Ainf p O), hw.symm⟩) N
  have hunit : IsUnit (fontaineTheta O p (↑u⁻¹ : Ainf p O)) := (Units.isUnit u⁻¹).map _
  refine ⟨fun σ => algebraMap O C (fontaineTheta O p (↑u⁻¹ : Ainf p O)) ^ a σ * c σ, ?_, ?_, ?_⟩
  · obtain ⟨h1, g, hg, hg2⟩ := hD
    exact ⟨h1.trans hmd, g, hg, hg2.trans hxd⟩
  · intro σ f hf
    obtain ⟨h1, h2, s, t, hs, hst, ht⟩ := hH σ f hf
    refine ⟨h1, mul_ne_zero (pow_ne_zero _ (hunit.map _).ne_zero) h2, s,
      (inA (↑u⁻¹ : Ainf p O) : RL p O Λ) ^ a σ * t, hs, ?_, ?_⟩
    · rw [hst, ← hu, ← mul_assoc, ← mul_pow, ← map_mul, mul_assoc, Units.mul_inv, mul_one]
    · simp only [RingHom.comp_apply, map_mul, map_pow] at ht ⊢
      rw [key σ f hf, ht]
      ring
  · intro σ
    simp only [map_mul, map_pow, hv.one_of_isUnit hunit, one_pow, one_mul]

end GlobalTheory
