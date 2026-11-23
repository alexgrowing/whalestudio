import Mathlib
import Formalism.CMTypeGalois.StatementField

open NumberField Finset

noncomputable section

namespace Formalism.Q3

open Classical in
theorem hostEmb_of (hC : HostConj) (hH : HostGalois) : HostEmb := by
  intro q hq E _ _ α hα φ₀
  obtain ⟨hGal, hfin, hbij, hmul⟩ := hH q hq E α hα
  have := hGal
  have hconj := (hC q hq E α hα).1
  set F : Gal(E/ℚ) → (E →+* ℂ) := fun σ => φ₀.comp σ.toAlgHom.toRingHom with hF
  have hinj : Function.Injective F := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    have := congrArg (fun f : E →+* ℂ => f x) h
    exact φ₀.injective this
  have hcard : Fintype.card Gal(E/ℚ) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  have hcc : ∀ σ τ : Gal(E/ℚ), galSign α τ = cc →
      F (τ * σ) = ComplexEmbedding.conjugate (F σ) := by
    intro σ τ hτ
    have h1 := (hconj φ₀ τ).mpr hτ
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1 (σ y)
  refine ⟨hFbij, hcc, ?_⟩
  intro Φ
  obtain ⟨τc, hτc⟩ := hbij.2 cc
  have hmem : ∀ σ, F σ ∈ (univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image F ↔
      galSign α σ ∈ Φ := by
    intro σ
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, he⟩
      rwa [← hinj he]
    · intro h
      exact ⟨σ, h, rfl⟩
  constructor
  · intro hΦ ψ
    obtain ⟨σ, rfl⟩ := hFbij.2 ψ
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc]
    exact hΦ _
  · intro hT g
    obtain ⟨σ, rfl⟩ := hbij.2 g
    have := hT (F σ)
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc] at this
    exact this

end Formalism.Q3
