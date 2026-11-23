import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernelStatement
open Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.commute_on_ker_of_commute_on_ker_inter :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ), (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((η g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = (((η * η₀) g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → ∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∀ g, η₀ g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n ρ₀ η₀ η hη hηη₀ Y hY g hg
  obtain ⟨Y₁, Y₂, rfl, h₁, h₂⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ η₀.ker 1 η Y
      (fun g hg h1 => by simpa using hY g (MonoidHom.mem_ker.mp hg) h1)
  obtain ⟨A, B, hAB, hA, hB⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ ⊤ η η₀ Y₂
      (fun g _ h1 => by simpa using h₂ g (MonoidHom.mem_ker.mpr h1))
  have hA0 : A = 0 := hη A (fun g => hA g (Subgroup.mem_top g))
  have hB0 : B = 0 := hηη₀ B (fun g => hB g (Subgroup.mem_top g))
  have hY₂ : Y₂ = 0 := by rw [hAB, hA0, hB0, add_zero]
  subst hY₂
  simpa using h₁ g (MonoidHom.mem_ker.mpr hg)

end GlobalTheory
