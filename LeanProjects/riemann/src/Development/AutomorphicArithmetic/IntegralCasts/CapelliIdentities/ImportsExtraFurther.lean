import Mathlib

namespace UpperTheory.Reformulated.B.AddCharacterCount.Helpers

private lemma card_le {C F : Type} [Field C] [Fintype F] [AddCommGroup F] :
    Finite (AddChar F C) ∧ Nat.card (AddChar F C) ≤ Nat.card F := by
  have li : LinearIndependent C (M := Multiplicative F → C)
      ((fun f => f : (Multiplicative F →* C) → Multiplicative F → C) ∘ AddChar.toMonoidHomEquiv) :=
    (linearIndependent_monoidHom (Multiplicative F) C).comp _ AddChar.toMonoidHomEquiv.injective
  have h1 := li.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hlt : Cardinal.mk (AddChar F C) < Cardinal.aleph0 :=
    lt_of_le_of_lt h1 Cardinal.natCast_lt_aleph0
  have hfin : Finite (AddChar F C) := Cardinal.lt_aleph0_iff_finite.mp hlt
  refine ⟨hfin, ?_⟩
  have : Nat.card (AddChar F C) ≤ Fintype.card (Multiplicative F) := by
    have h2 := Cardinal.toNat_le_toNat h1 Cardinal.natCast_lt_aleph0
    simpa [Nat.card] using h2
  simpa [Nat.card_eq_fintype_card] using this

end UpperTheory.Reformulated.B.AddCharacterCount.Helpers

open UpperTheory.Reformulated.B.AddCharacterCount.Helpers in
theorem UpperTheory.Reformulated.B.AddCharacterCount.main :
    ∀ {C F : Type} [inst : Field C] [inst_1 : Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F C),
      ψ ≠ (1 : AddChar F C) →
        ∃ (e : F ≃ AddChar F C),
          (∀ (h h' : F), (e : F → AddChar F C) (h + h') = (e : F → AddChar F C) h * (e : F → AddChar F C) h') ∧
            ∀ (h a : F), ((e : F → AddChar F C) h : F → C) a = (ψ : F → C) (h * a) := by
  intro C F _ _ _ _ ψ hψ
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  obtain ⟨hfin, hc⟩ := card_le (C := C) (F := F)
  have hbij : Function.Bijective ψ.mulShift := hinj.bijective_of_nat_card_le hc
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro h h'
    simp [AddChar.mulShift_mul]
  · intro h a
    simp
