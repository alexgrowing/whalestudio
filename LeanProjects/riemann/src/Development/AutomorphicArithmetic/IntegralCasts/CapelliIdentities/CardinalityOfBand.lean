import Mathlib

noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
