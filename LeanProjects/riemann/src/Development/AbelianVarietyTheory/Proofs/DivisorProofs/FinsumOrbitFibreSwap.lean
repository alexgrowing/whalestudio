import Mathlib
open scoped BigOperators

namespace GlobalTheory
namespace OrbitFibre

open MulAction Function

theorem finsum_sigma_iter {ι : Type} {κ : ι → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (support f).Finite) : ∑ᶠ p, f p = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  set s := hf.toFinset with hs
  let t : Finset ι := s.image Sigma.fst
  let u : ∀ i, Finset (κ i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : s ⊆ t.sigma u := by
    intro p hp
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hp, by simpa [u] using hp⟩
  rw [finsum_eq_sum f hf, ← hs, Finset.sum_subset hsub ?_, Finset.sum_sigma]
  · rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
    · apply Finset.sum_congr rfl
      intro i _
      rw [finsum_eq_sum_of_support_subset _ (s := u i)]
      intro k hk
      simpa [u, hs] using hk
    · intro i hi
      rw [Function.mem_support] at hi
      by_contra hit
      apply hi
      have : ∀ k, f ⟨i, k⟩ = 0 := by
        intro k
        by_contra hk
        apply hit
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, k⟩, by simpa [hs] using hk, rfl⟩)
      simp [this]
  · intro p _ hp
    simpa [hs] using hp

variable {Γ A B J : Type} [Group Γ] [MulAction Γ A] [MulAction Γ B]

noncomputable def toOrbit (τ : J → B)
    (p : Σ j : J, orbitRel.Quotient (stabilizer Γ (τ j)) A) : orbitRel.Quotient Γ (A × B) :=
  Quotient.mk'' (Quotient.out p.2, τ p.1)

def liftW (Ψ : A → B → ℂ) (hΨ : ∀ (g : Γ) a b, Ψ (g • a) (g • b) = Ψ a b) :
    orbitRel.Quotient Γ (A × B) → ℂ :=
  Quotient.lift (fun p => Ψ p.1 p.2) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a, b) ∈ orbit Γ (a', b') := h
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp h'
    rw [Prod.smul_mk, Prod.mk.injEq] at hg
    obtain ⟨h1, h2⟩ := hg
    simp only
    rw [← h1, ← h2, hΨ])

variable (Γ A B) in

def swapQ : orbitRel.Quotient Γ (B × A) ≃ orbitRel.Quotient Γ (A × B) :=
  Quotient.congr (Equiv.prodComm B A) (by
    rintro ⟨b, a⟩ ⟨b', a'⟩
    change (b, a) ∈ orbit Γ (b', a') ↔ (a, b) ∈ orbit Γ (a', b')
    simp only [mem_orbit_iff, Prod.smul_mk, Prod.mk.injEq]
    exact ⟨fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩, fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩⟩)

end OrbitFibre

end GlobalTheory
