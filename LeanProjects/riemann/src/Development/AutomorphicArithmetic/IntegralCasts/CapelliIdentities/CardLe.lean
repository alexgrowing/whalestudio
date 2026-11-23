import Mathlib

namespace AddCharEqMulShift

private lemma card_le (F K : Type) [Field F] [Fintype F] [Field K] :
    Finite (AddChar F K) ∧ Nat.card (AddChar F K) ≤ Nat.card F := by
  have hli : LinearIndependent K
      (fun ψ : AddChar F K => ((AddChar.toMonoidHomEquiv ψ : Multiplicative F →* K) :
        Multiplicative F → K)) :=
    (linearIndependent_monoidHom (Multiplicative F) K).comp _
      AddChar.toMonoidHomEquiv.injective
  have hfin : Finite (AddChar F K) := hli.finite
  refine ⟨hfin, ?_⟩
  haveI : Fintype (AddChar F K) := Fintype.ofFinite _
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

end AddCharEqMulShift

theorem UpperTheory.Reformulated.B.Yde4.main :
    ∀ {F K : Type} [inst : Field F] [Fintype F] [inst_2 : Field K] (ψ₀ ψ : AddChar F K),
      ψ₀ ≠ (1 : AddChar F K) → ∃ (c : F), ψ = ψ₀.mulShift c := by
  intro F K _ _ _ ψ₀ ψ h
  obtain ⟨hfin, hle⟩ := AddCharEqMulShift.card_le F K
  have hinj : Function.Injective ψ₀.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hle).2 ψ
  exact ⟨c, hc.symm⟩
