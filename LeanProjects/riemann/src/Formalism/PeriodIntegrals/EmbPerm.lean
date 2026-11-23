import Mathlib

noncomputable section

namespace PI

open Classical

def EmbPermDefs.liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0

def EmbPermDefs.cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (EmbPermDefs.liftM M x)

def EmbPerm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      (∀ a : K, φ₀ (a : E) ∈ M ∧ EmbPermDefs.cj M ρ (φ₀ (a : E)) = φ₀ (a : E)) → (∀ s x, emb s x ∈ M) →
      ∃ π : Equiv.Perm S, ∀ s x, EmbPermDefs.cj M ρ (emb s x) = emb (π s) x

end PI
