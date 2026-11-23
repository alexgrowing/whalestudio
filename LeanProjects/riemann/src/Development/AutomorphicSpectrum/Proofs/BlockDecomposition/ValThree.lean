import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ValThree

theorem val_three : ∀ (B : Type) [CommRing B] (π : B), VAL π → ∀ (f g : B) (M : ℕ), ∃ e₁ e₂ e : B, IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧ IsIdempotentElem e ∧ e₁ * f ∈ Ideal.span {π ^ M} ∧ (1 - e₁) * π ^ M ∈ Ideal.span {f} ∧ e₂ * g ∈ Ideal.span {π ^ M} ∧ (1 - e₂) * π ^ M ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * e * f ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * (1 - e) * g ∈ Ideal.span {f} := by
  intro B _ π hV f g M
  have hpair : ∀ x : B, π ^ M ∈ Ideal.span {x, π ^ M} := fun x => Ideal.subset_span (by simp)
  obtain ⟨e₁, he₁, h1a, h1b⟩ := hV f (π ^ M) ⟨M, hpair f⟩
  obtain ⟨e₂, he₂, h2a, h2b⟩ := hV g (π ^ M) ⟨M, hpair g⟩
  have i₁ : e₁ * e₁ = e₁ := he₁
  have i₂ : e₂ * e₂ = e₂ := he₂
  have he₃1 : (1 - e₁) * (1 - e₂) * (1 - e₁) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₂) * i₁
  have he₃2 : (1 - e₁) * (1 - e₂) * (1 - e₂) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₁) * i₂
  have he₃ : (1 - e₁) * (1 - e₂) * ((1 - e₁) * (1 - e₂)) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₂) * he₃1 + he₃2
  generalize hE : (1 - e₁) * (1 - e₂) = E at he₃1 he₃2 he₃ ⊢
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp h1b
  have hM : π ^ M ∈ Ideal.span {E * f + (1 - E), E * g + (1 - E)} := by
    rw [Ideal.mem_span_pair]
    refine ⟨E * h + (1 - E) * π ^ M, 0, ?_⟩
    linear_combination (h * f - h - π ^ M * f + π ^ M) * he₃ + E * hh + π ^ M * he₃1
  obtain ⟨e, he, ha, hb⟩ := hV (E * f + (1 - E)) (E * g + (1 - E)) ⟨M, hM⟩
  obtain ⟨a, ha'⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b, hb'⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨e₁, e₂, e, he₁, he₂, he, h1a, h1b, h2a, h2b, ?_, ?_⟩
  · rw [hE]
    refine Ideal.mem_span_singleton'.mpr ⟨a * E, ?_⟩
    linear_combination E * ha' - (a * (g - 1) - e * (f - 1)) * he₃
  · rw [hE]
    refine Ideal.mem_span_singleton'.mpr ⟨b * E, ?_⟩
    linear_combination E * hb' - (b * (f - 1) - (1 - e) * (g - 1)) * he₃

end GlobalTheory.CompanionTheory.ValThree
