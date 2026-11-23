import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj

theorem not_eq_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) (h : ∀ a : 𝓞 E, σ τ a = star (σ τ' a)) : False := by
  have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := RingHom.ext h
  exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩

theorem emb_eq_star_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (i k : Ix Ψ j j') :
    (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  obtain ⟨s, τ⟩ := i
  obtain ⟨t, τ'⟩ := k
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.isLeft_inl, ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ τ' h
    | inr t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, star_star, ne_eq, Bool.true_eq_false, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext h)
      · rintro rfl a
        rfl
  | inr s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, ne_eq, Bool.false_eq_true, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext fun a => star_injective (h a))
      · rintro rfl a
        rfl
    | inr t =>
      simp only [emb, Sum.elim_inr, Sum.isLeft_inr, RingHom.comp_apply, starRingEnd_apply, star_star,
        ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ' τ fun a => (h a).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj
