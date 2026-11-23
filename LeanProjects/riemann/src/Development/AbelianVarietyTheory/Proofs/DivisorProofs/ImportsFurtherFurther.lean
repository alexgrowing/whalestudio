import Mathlib

namespace GlobalTheory.SpectralLemmaFirst

theorem main : (let d1 : {V ι : Type} → [inst : AddCommGroup V] → [inst_1 : Module ℂ V] → (ι → V →ₗ[ℂ] V) → Subalgebra ℂ (Module.End ℂ V) := @(fun {V ι : Type} [AddCommGroup V] [Module ℂ V] (ρ : ι → V →ₗ[ℂ] V) ↦ Algebra.adjoin ℂ (Set.range ρ)); ∀ {V ι : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] {ρ : ι → V →ₗ[ℂ] V} {N : Submodule ℂ V}, (∀ (y : ι), ∀ x ∈ N, (ρ y : V → V) x ∈ N) → ∀ {s : Module.End ℂ V}, s ∈ d1 ρ → ∀ x ∈ N, (s : V → V) x ∈ N) := by
  intro d1 V ι _ _ ρ N hN s hs
  simp only [d1] at hs
  induction hs using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    exact hN y
  | algebraMap r =>
    intro x hx
    simpa [Module.algebraMap_end_apply] using N.smul_mem r hx
  | add f g _ _ hf hg =>
    intro x hx
    simpa using N.add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg =>
    intro x hx
    simpa using hf _ (hg x hx)

end GlobalTheory.SpectralLemmaFirst
