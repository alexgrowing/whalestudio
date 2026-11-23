import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private def chOne {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) :
    Ch Ω c 1 ≃ ((Γ ⧸ Subgroup.zpowers c) →* Ωˣ) where
  toFun χ := QuotientGroup.lift (Subgroup.zpowers c) χ.1 (by
    have h : χ.1 c = 1 := Units.ext (by simpa using χ.2)
    rintro _ ⟨n, rfl⟩
    simp [h])
  invFun ψ := ⟨ψ.comp (QuotientGroup.mk' _), by
    have h : (QuotientGroup.mk c : Γ ⧸ Subgroup.zpowers c) = 1 :=
      (QuotientGroup.eq_one_iff c).2 (Subgroup.mem_zpowers c)
    simp [h]⟩
  left_inv χ := Subtype.ext (MonoidHom.ext fun g => rfl)
  right_inv ψ := MonoidHom.ext fun g => by
    induction g using QuotientGroup.induction_on with
    | H g => rfl

private def chMul {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (χ₀ : Ch Ω c ε) :
    Ch Ω c 1 ≃ Ch Ω c ε where
  toFun χ := ⟨χ₀.1 * χ.1, by simp [χ₀.2, χ.2]⟩
  invFun χ := ⟨χ₀.1⁻¹ * χ.1, by
    have h : χ.1 c = χ₀.1 c := Units.ext (χ.2.trans χ₀.2.symm)
    simp [h]⟩
  left_inv χ := Subtype.ext (inv_mul_cancel_left _ _)
  right_inv χ := Subtype.ext (mul_inv_cancel_left _ _)

theorem UpperTheory.V.B5.card_signedInvolutionChar_eq_card_involutionQuotient :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → Fintype.card (Ch Ω c ε) = Fintype.card (Qc c) := by
  intro Ω _ Γ _ _ _ c ε h2 hc hε
  classical
  have hne₀ : Nonempty (Ch Ω c ε) := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hε with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨⟨1, by simp⟩⟩
    · obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Γ Ω hc
      refine ⟨⟨φ, ?_⟩⟩
      have hsq : (φ c : Ω) * (φ c : Ω) = 1 := by
        rw [← Units.val_mul, ← map_mul, h2, map_one, Units.val_one]
      have hne : (φ c : Ω) ≠ 1 := fun h => hφ (Units.ext (by simpa using h))
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact absurd h hne
      · simpa using h
  obtain ⟨χ₀⟩ := hne₀
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity Ω (Monoid.exponent (Γ ⧸ Subgroup.zpowers c)) :=
    HasEnoughRootsOfUnity.of_dvd Ω (Group.exponent_quotient_dvd _)
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.card_congr ((chMul c ε χ₀).symm.trans (chOne c)),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  rfl
