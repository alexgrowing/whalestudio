import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula

namespace GlobalTheory.FlagCurve

theorem card_filter_fin_val_lt (N j : ℕ) (h : j ≤ N) :
    (Finset.univ.filter fun a : Fin N => (a : ℕ) < j).card = j := by
  rw [← Finset.card_map Fin.valEmbedding]
  rw [show (Finset.univ.filter fun a : Fin N => (a : ℕ) < j).map Fin.valEmbedding = Finset.range j by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩]
  simp

theorem card_filter_fin_le_val (N j : ℕ) :
    (Finset.univ.filter fun b : Fin N => j ≤ (b : ℕ)).card = N - j := by
  rw [← Finset.card_map Fin.valEmbedding]
  rw [show (Finset.univ.filter fun b : Fin N => j ≤ (b : ℕ)).map Fin.valEmbedding = Finset.Ico j N by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩]
  simp

theorem crSet_eq_product (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) :
    crSet ι N j = Finset.univ ×ˢ ((Finset.univ.filter fun a : Fin N => (a : ℕ) < j) ×ˢ
      (Finset.univ.filter fun b : Fin N => j ≤ (b : ℕ))) := by
  ext ⟨τ, a, b⟩
  simp only [crSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨Fin.lt_def.2 (lt_of_lt_of_le h1 h2), h1, h2⟩

theorem card_crSet_eq_dimGr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), j ≤ N →
    (crSet ι N j).card = dimGr ι N j := by
  intro ι _ _ N j h
  rw [crSet_eq_product, Finset.card_product, Finset.card_product, Finset.card_univ,
    card_filter_fin_val_lt N j h, card_filter_fin_le_val N j]
  rfl

end GlobalTheory.FlagCurve
