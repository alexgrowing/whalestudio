import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

open IsLocalRing

theorem UpperTheory.V.CA.g_ratliff :
    ∀ (P Q : Type) [CommRing P] [CommRing Q] [IsNoetherianRing P] [IsNoetherianRing Q] [Algebra P Q] [Module.Flat P Q] (n : ℕ),
      ReciprocityTheory.CA.DimFormula P → ReciprocityTheory.CA.DimFormula Q → ringKrullDim P = n → ringKrullDim Q = n →
        ∀ (q : Ideal P) [q.IsPrime], ∀ Q' ∈ (q.map (algebraMap P Q)).minimalPrimes,
          Q'.comap (algebraMap P Q) = q ∧ ringKrullDim (Q ⧸ Q') = ringKrullDim (P ⧸ q) := by
  intro P Q _ _ _ _ _ _ n hP hQ dP dQ q _ Q' hQ'
  have hprime : Q'.IsPrime := hQ'.1.1
  have hle : q.map (algebraMap P Q) ≤ Q' := hQ'.1.2
  have hle' : q ≤ Q'.under P := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P₁, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := Q'.under P) Q' hle'
  have h4 : q.map (algebraMap P Q) ≤ P₁ := Ideal.map_le_iff_le_comap.mpr h3.over.le
  have h5 : P₁ = Q' := le_antisymm h1 (hQ'.2 ⟨h2, h4⟩ h1)
  subst h5
  refine ⟨h3.over.symm, ?_⟩
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q P₁
  have hpm : (P₁.map (Ideal.Quotient.mk (q.map (algebraMap P Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using h4)
  have h0 : (P₁.map (Ideal.Quotient.mk (q.map (algebraMap P Q)))).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    have := Ideal.minimalPrimes_map_of_surjective
      (f := Ideal.Quotient.mk (q.map (algebraMap P Q))) Ideal.Quotient.mk_surjective ⊥
    rw [Ideal.map_bot, bot_sup_eq, Ideal.mk_ker] at this
    change _ ∈ (⊥ : Ideal _).minimalPrimes
    rw [this]
    exact ⟨P₁, hQ', rfl⟩
  rw [h0, add_zero] at hh
  have e1 := hP q
  have e2 := hQ P₁
  rw [dP] at e1
  rw [dQ, hh, ← e1] at e2
  have hne : q.height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at e2
  generalize ringKrullDim (Q ⧸ P₁) = a at e2
  generalize ringKrullDim (P ⧸ q) = b at e2
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => rfl
    | coe b =>
      rw [WithBot.add_bot, ← WithBot.coe_add] at e2
      exact absurd e2 WithBot.bot_ne_coe
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot, ← WithBot.coe_add] at e2
      exact absurd e2 WithBot.coe_ne_bot
    | coe b =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at e2
      rw [WithTop.add_left_cancel (ENat.coe_ne_top k) e2]
