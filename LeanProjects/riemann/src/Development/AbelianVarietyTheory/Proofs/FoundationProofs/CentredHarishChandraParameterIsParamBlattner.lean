import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.HarmonicParam

variable {p q : ℕ}

theorem card_filter_sum (P : Ix p q → Prop) [DecidablePred P] (A : Finset (Fin p)) (B : Finset (Fin q))
    (hA : ∀ i, P (Sum.inl i) ↔ i ∈ A) (hB : ∀ j, P (Sum.inr j) ↔ j ∈ B) :
    (Finset.univ.filter P).card = A.card + B.card := by
  rw [← Finset.card_disjSum]
  congr 1
  ext x
  cases x <;> simp [hA, hB]

theorem rhoNC_of_strictAnti (lam : Ix p q → ℚ) (h1 : StrictAnti fun i => lam (Sum.inl i))
    (h2 : StrictAnti fun j => lam (Sum.inr j)) (h3 : ∀ i j, lam (Sum.inr j) < lam (Sum.inl i)) :
    (∀ i : Fin p, rhoNC lam (Sum.inl i) = (q : ℚ) / 2 - ((p : ℚ) - 1 - 2 * (i.1 : ℚ)) / 2) ∧
    (∀ j : Fin q, rhoNC lam (Sum.inr j) = -(p : ℚ) / 2 - ((q : ℚ) - 1 - 2 * (j.1 : ℚ)) / 2) := by
  have h1' : ∀ i i', lam (Sum.inl i) < lam (Sum.inl i') ↔ i' < i := fun i i' => h1.lt_iff_gt
  have h2' : ∀ i i', lam (Sum.inr i) < lam (Sum.inr i') ↔ i' < i := fun i i' => h2.lt_iff_gt
  have h4 : ∀ i j, ¬ lam (Sum.inl i) < lam (Sum.inr j) := fun i j => (h3 i j).not_gt
  constructor
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ Finset.univ (by simp [sameBlock]) (by simp [sameBlock, h3]),
      card_filter_sum _ ∅ ∅ (by simp [sameBlock]) (by simp [sameBlock, h4]),
      card_filter_sum _ (Finset.Ioi i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock]),
      card_filter_sum _ (Finset.Iio i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock])]
    have hi : i.1 + 1 ≤ p := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ ∅ (by simp [sameBlock, h4]) (by simp [sameBlock]),
      card_filter_sum _ Finset.univ ∅ (by simp [sameBlock, h3]) (by simp [sameBlock]),
      card_filter_sum _ ∅ (Finset.Ioi i) (by simp [sameBlock]) (by simp [sameBlock, h2']),
      card_filter_sum _ ∅ (Finset.Iio i) (by simp [sameBlock]) (by simp [sameBlock, h2'])]
    have hi : i.1 + 1 ≤ q := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

theorem hcParam_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) →
    IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧
    ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  intro p q n hn ap am hap ham _ _
  have hn' : (p : ℚ) + q + 1 ≤ n := by exact_mod_cast hn
  have h1 : StrictAnti fun i => hcParam n ap am (Sum.inl i) := by
    intro i j hij
    have a : (ap j : ℚ) ≤ ap i := by exact_mod_cast hap hij.le
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h2 : StrictAnti fun i => hcParam n ap am (Sum.inr i) := by
    intro i j hij
    have a : (am i.rev : ℚ) ≤ am j.rev := by exact_mod_cast ham (Fin.rev_le_rev.2 hij.le)
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h3 : ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
    intro i j
    have a : (0 : ℚ) ≤ ap i := Nat.cast_nonneg _
    have b : (0 : ℚ) ≤ am j.rev := Nat.cast_nonneg _
    have c : (0 : ℚ) ≤ j.1 := Nat.cast_nonneg _
    have d : (i.1 : ℚ) + 1 ≤ p := by exact_mod_cast i.2
    simp only [hcParam]
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h3⟩
  · rintro (a | a) (b | b) h
    · rw [h1.injective h]
    · exact absurd h (h3 a b).ne'
    · exact absurd h (h3 b a).ne
    · rw [h2.injective h]
  · rintro (a | a) (b | b) h
    · exact h1 h
    · exact h.elim
    · exact h.elim
    · exact h2 h
  · rintro (a | a)
    · exact ⟨2 * (ap a) + 2 * (p - (a.1 + 1)) + (n - p - q + 1), by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-2 * (am a.rev) - 2 * (a.1 + 1) - (n - p - q - 1), by simp only [hcParam]; push_cast; ring⟩
  · rintro (a | a) (b | b)
    · exact ⟨ap a - ap b - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨ap a + (p - (a.1 + 1)) + am b.rev + (b.1 + 1) + (n - p - q),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-(ap b + (p - (b.1 + 1)) + am a.rev + (a.1 + 1) + (n - p - q)),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨am b.rev - am a.rev - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
  · obtain ⟨r1, r2⟩ := rhoNC_of_strictAnti _ h1 h2 h3
    funext a
    rcases a with a | a
    · simp only [blattner, r1, hcParam, wtK]
      ring
    · simp only [blattner, r2, hcParam, wtK]
      ring

end GlobalTheory.HarmonicParam
