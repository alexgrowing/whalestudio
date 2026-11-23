import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.LtHalfPredOfLog

open NumberField

namespace KStar.Choice

noncomputable def rootNu (E : Type*) [Field E] [NumberField E] (l : ℕ) : ℕ :=
  padicValNat l (Units.torsionOrder E)

noncomputable def rootDeg (E : Type*) [Field E] (l : ℕ) : ℕ :=
  Module.finrank E (CyclotomicField l E)

def RamLE (E : Type*) [Field E] [NumberField E] (l e : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 E), P.IsPrime ∧ P.LiesOver (Ideal.span {(l : ℤ)}) ∧ P.ramificationIdx ℤ ≤ e

variable (E : Type*) [Field E] [NumberField E] {l : ℕ}

private theorem rootNu_pos_iff (hl : l.Prime) : 0 < rootNu E l ↔ l ∣ Units.torsionOrder E := by
  have := Fact.mk hl
  unfold rootNu
  rw [Nat.pos_iff_ne_zero, ne_eq, padicValNat.eq_zero_iff]
  have h1 := hl.one_lt
  have h2 := Units.torsionOrder_pos E
  constructor
  · intro h
    by_contra h'
    exact h (Or.inr (Or.inr h'))
  · rintro h (h' | h' | h')
    · omega
    · omega
    · exact h' h

theorem rootDeg_dvd (hl : l.Prime) :
    rootDeg E l ∣ l - 1 ∧ (rootDeg E l = 1 ↔ 0 < rootNu E l) := by
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : FiniteDimensional E (CyclotomicField l E) :=
    IsCyclotomicExtension.finiteDimensional {l} E _
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hc : Nat.card (CyclotomicField l E ≃ₐ[E] CyclotomicField l E) = rootDeg E l :=
    IsGalois.card_aut_eq_finrank E _
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.card_dvd_of_injective _ (hz.autToPow_injective E)
    rwa [hc, Nat.card_eq_fintype_card, ZMod.card_units] at h
  · intro h
    rw [rootNu_pos_iff E hl]
    have hb : (⊥ : Subalgebra E (CyclotomicField l E)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one h
    have hm : IsCyclotomicExtension.zeta l E (CyclotomicField l E) ∈
        (⊥ : Subalgebra E (CyclotomicField l E)) := hb ▸ Algebra.mem_top
    obtain ⟨y, hy⟩ := Algebra.mem_bot.1 hm
    rw [← hy] at hz
    exact Units.dvd_torsionOrder_of_isPrimitiveRoot
      (hz.of_map_of_injective (algebraMap E (CyclotomicField l E)).injective)
  · intro h
    rw [rootNu_pos_iff E hl] at h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Units.torsion E) l h
    have h1 : IsPrimitiveRoot x l := hx ▸ IsPrimitiveRoot.orderOf x
    have h3 : IsPrimitiveRoot (x : (𝓞 E)ˣ) l :=
      h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective
    have h4 : IsPrimitiveRoot ((x : (𝓞 E)ˣ) : 𝓞 E) l := IsPrimitiveRoot.coe_units_iff.mpr h3
    have h5 : IsPrimitiveRoot (algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E)) l :=
      h4.map_of_injective (RingOfIntegers.coe_injective)
    generalize algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E) = y at h5
    have h6 : IsPrimitiveRoot (algebraMap E (CyclotomicField l E) y) l :=
      h5.map_of_injective (algebraMap E (CyclotomicField l E)).injective
    rw [← hc, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun σ τ => h6.autToPow_injective E ?_⟩, ⟨1⟩⟩
    apply Units.ext
    apply ZMod.val_injective
    apply h6.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [h6.autToPow_spec E σ, h6.autToPow_spec E τ, σ.commutes, τ.commutes]

private theorem prime_sub_one_le_ramification_degree {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra E L] {l : ℕ} (hl : l.Prime) {z : L} (hz : IsPrimitiveRoot z l) (P : Ideal (𝓞 E))
    [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    l - 1 ≤ P.ramificationIdx ℤ * Module.finrank E L := by
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hc : IsCyclotomicExtension {l} ℚ (IntermediateField.adjoin ℚ {z}) :=
    hz.intermediateField_adjoin_isCyclotomicExtension ℚ
  set R := Q.under (𝓞 (IntermediateField.adjoin ℚ {z}))
  have hR : R.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.tower_bot Q R _
  have h1 := Ideal.ramificationIdx_below_dvd (R := ℤ) R Q
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime l _ R] at h1
  have h2 := Nat.le_of_dvd (Ideal.ramificationIdx_pos _ _) h1
  rw [Ideal.ramificationIdx_tower (R := ℤ) P Q] at h2
  refine h2.trans (Nat.mul_le_mul_left _ ?_)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(l : ℤ)}) (by simpa using hl.ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have h3 := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L] at h3
  rw [← h3]
  refine le_trans ?_ (Finset.single_le_sum (f := fun q : P.primesOver (𝓞 L) =>
    q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Q, hQ1, hQ2⟩))
  exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos _ _)

theorem RamLE.pred_le {E : Type*} [Field E] [NumberField E] {l e : ℕ} (hl : l.Prime)
    (h : RamLE E l e) : l - 1 ≤ e * rootDeg E l := by
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨P, hP, hPl, he⟩ := h
  have : NumberField (CyclotomicField l E) := IsCyclotomicExtension.numberField {l} E _
  exact (prime_sub_one_le_ramification_degree hl (IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)) P).trans
    (Nat.mul_le_mul_right _ he)

theorem rootData_field {S L : Finset ℕ} (hS : ∀ l ∈ S, l.Prime)
    (hunr : ∀ l, l.Prime → l ≠ 2 → l ∉ S → l ∉ L → RamLE E l 1)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 < l ∧ RamLE E l 2) :
    RootData S L (rootNu E) (rootDeg E) where
  prime_small := hS
  nu_two := (rootNu_pos_iff E Nat.prime_two).2 (Units.even_torsionOrder E).two_dvd
  one_lt := fun l hl h0 => by
    obtain ⟨h1, h2⟩ := rootDeg_dvd E hl
    have h3 := hl.two_le
    have h4 : 0 < rootDeg E l := Nat.pos_of_dvd_of_pos h1 (by omega)
    have h5 : rootDeg E l ≠ 1 := fun h => by have := h2.1 h; omega
    omega
  unramified := fun l hl h2 h3 h4 => by
    obtain ⟨h5, h6⟩ := rootDeg_dvd E hl
    have h7 := (hunr l hl h2 h3 h4).pred_le hl
    have h8 := hl.two_le
    have h9 := Nat.le_of_dvd (by omega) h5
    refine ⟨?_, by omega⟩
    by_contra h0
    have := h6.2 (Nat.pos_of_ne_zero h0)
    omega
  large := fun l hm => by
    obtain ⟨hl, h3, h4⟩ := hL l hm
    have h7 := h4.pred_le hl
    refine ⟨?_, by omega⟩
    by_contra h0
    have := (rootDeg_dvd E hl).2.2 (Nat.pos_of_ne_zero h0)
    omega
  small := fun l hm => (rootDeg_dvd E (hS l hm)).1

end KStar.Choice
