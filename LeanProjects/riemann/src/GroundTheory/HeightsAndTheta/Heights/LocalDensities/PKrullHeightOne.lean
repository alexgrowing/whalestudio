import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsKrullHeightOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open Ideal

theorem KrullHeightOne.exists_prime_colon {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p q : A) (hqp : ¬ q ∣ p) :
    ∃ (a : A) (P : Ideal A), P.IsPrime ∧ ¬ q ∣ a * p ∧ ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
  let mk := Ideal.Quotient.mk (Ideal.span {q})
  let M := Submodule.span A {mk p}
  have hx : (⟨mk p, Submodule.mem_span_singleton_self _⟩ : M) ≠ 0 := by
    intro h
    apply hqp
    have : mk p = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hx
  obtain ⟨hPp, y, hy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
  have key : ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
    intro x
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.val_inj]
    change x • (y : A ⧸ Ideal.span {q}) = 0 ↔ _
    rw [← ha, smul_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_assoc]
  refine ⟨a, P, hPp, fun h => hPp.ne_top ?_, key⟩
  rw [Ideal.eq_top_iff_one, key, one_mul]
  exact h

theorem KrullHeightOne.proof : KrullHeightOne.Statement := by
  intro A _ _ _ _ p q hpq
  obtain ⟨hq, hqp⟩ := hpq
  obtain ⟨a, P, hPp, hb, hP⟩ := KrullHeightOne.exists_prime_colon p q hqp
  have hqP : q ∈ P := (hP q).2 (dvd_mul_right q _)
  have hPbot : P ≠ ⊥ := fun h => hq (by rw [h, Ideal.mem_bot] at hqP; exact hqP)

  have hex : ∃ u ∈ P, ∃ w ∉ P, u * (a * p) = q * w := by
    by_contra hne
    have hne' : ∀ u ∈ P, ∀ w, u * (a * p) = q * w → w ∈ P := by
      intro u hu w huw
      by_contra hw
      exact hne ⟨u, hu, w, hw, huw⟩
    have hqK : algebraMap A (FractionRing A) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hq
    let N : Submodule A (FractionRing A) := Submodule.map (Algebra.linearMap A (FractionRing A)) P
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A (FractionRing A) q ∈ N := Submodule.mem_map_of_mem hqP
      rw [h, Submodule.mem_bot] at this
      exact hqK this
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hy : IsIntegral A (algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q) := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg _ ?_
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hP x).1 hx
      have hwP : w ∈ P := hne' x hx w hw
      refine Submodule.mem_map.2 ⟨w, hwP, ?_⟩
      show algebraMap A (FractionRing A) w =
        algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q *
          algebraMap A (FractionRing A) x
      rw [div_mul_eq_mul_div, eq_div_iff hqK, ← map_mul, ← map_mul, mul_comm (a * p) x, hw,
        mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy
    apply hb
    refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul _ q z, hz]
    exact (mul_div_cancel₀ _ hqK).symm
  obtain ⟨u, hu, w, hw, huw⟩ := hex

  have hmin : P ∈ (Ideal.span {u}).minimalPrimes := by
    refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hu⟩, ?_⟩
    rintro Q ⟨hQ, huQ⟩ hQP x hx
    obtain ⟨v, hv⟩ := (hP x).1 hx
    have h1 : x * w = u * v := by
      apply mul_left_cancel₀ hq
      linear_combination (-x) * huw + u * hv
    have h2 : x * w ∈ Q := by
      rw [h1]
      exact Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem _).1 huQ)
    rcases hQ.mem_or_mem h2 with h | h
    · exact h
    · exact absurd (hQP h) hw
  have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
  have := hPp
  have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hge : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.2 fun h => hPbot (Ideal.height_eq_zero_iff_eq_bot.1 h)
  refine ⟨P, hPp, le_antisymm hle hge, w, hw, u * a, P.mul_mem_right a hu, ?_⟩
  linear_combination -huw

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
