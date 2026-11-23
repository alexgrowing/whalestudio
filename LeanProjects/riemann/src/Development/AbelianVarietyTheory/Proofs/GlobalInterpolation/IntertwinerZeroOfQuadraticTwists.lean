import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernelStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEqStatement
open Formalism.MainNotions.N

namespace GlobalTheory

theorem trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  intro Γ k _ _ _ n ρ₀ ρ ρ' η₀ χ₁ χ₂ hρ hρ' hs hs' hno htr
  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq Γ k n ρ ρ' χ₁ χ₂ hs hs' htr
  have hzero : ∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂) →
      ∀ X : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ (⊤ : Subgroup Γ), ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        ((c g : ℤ) : k) • (X * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0 := by
    intro c hc X hX
    obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ₀ ρ₀ ⊤ c η₀ X (by
      intro g hg h
      have := hX g hg
      rwa [hρ g h, hρ' g h] at this)
    have hA0 : A = 0 := hno c (by tauto) A (fun g => hA g trivial)
    have hB0 : B = 0 := hno (c * η₀) (by rcases hc with rfl | rfl | rfl <;> simp) B
      (fun g => hB g trivial)
    rw [hAB, hA0, hB0, add_zero]
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ χ₂.ker 1 χ₁
    (P : Matrix (Fin n) (Fin n) k) (by
      intro g hg h
      have h1 : ρ g * P = P * ρ' g := by rw [hP g h hg]; group
      have h2 := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) h1
      simpa using h2)
  obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ 1 χ₂ Y₁ (fun g _ h => hY₁ g h)
  obtain ⟨C, D, hCD, hC, hD⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ (1 * χ₁) χ₂ Y₂ (fun g _ h => hY₂ g h)
  have hB0 : B = 0 := hzero _ (by simp) B hB
  have hC0 : C = 0 := hzero _ (by simp) C hC
  have hD0 : D = 0 := hzero _ (by simp) D hD
  have hPA : (P : Matrix (Fin n) (Fin n) k) = A := by
    rw [hY, hAB, hCD, hB0, hC0, hD0]; simp
  intro g
  have h1 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    have := hA g trivial
    rw [← hPA] at this
    simpa using this
  have h2 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  rw [h2, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

end GlobalTheory
