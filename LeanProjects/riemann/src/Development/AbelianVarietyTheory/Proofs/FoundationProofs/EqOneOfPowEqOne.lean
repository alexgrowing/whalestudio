import Mathlib

namespace GlobalTheory.RootOfUnityEqOne

open IsLocalRing

theorem eq_one_of_pow_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ}
    (hm : V.valuation (m : F) = 1) {ζ : F} (hζ : ζ ^ m = 1)
    (h1 : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  have hζV : ζ ∈ V := by
    apply V.mem_of_valuation_le_one
    have : ζ = (ζ - 1) + 1 := by ring
    rw [this]
    refine le_trans (Valuation.map_add _ _ _) (max_le h1.le ?_)
    simp
  set z : V := ⟨ζ, hζV⟩ with hz
  have hzm : z ^ m = 1 := Subtype.ext (by simpa [hz] using hζ)
  have hz1 : z - 1 ∈ maximalIdeal V := by
    rw [V.valuation_lt_one_iff]
    simpa [hz] using h1
  have hmu : IsUnit (m : V) := by
    rw [V.valuation_eq_one_iff]
    simpa using hm
  have hmI : (m : V) ∉ maximalIdeal V := fun h => (mem_maximalIdeal _).1 h hmu

  have hdiff : ∀ n : ℕ, (∑ i ∈ Finset.range n, z ^ i) - (n : V) ∈ maximalIdeal V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp : z ^ n - 1 ∈ maximalIdeal V := by
        have : z - 1 ∣ z ^ n - 1 := sub_one_dvd_pow_sub_one z n
        obtain ⟨c, hc⟩ := this
        rw [hc]
        exact Ideal.mul_mem_right _ _ hz1
      have : (∑ i ∈ Finset.range n, z ^ i) + z ^ n - ((n + 1 : ℕ) : V)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : V)) + (z ^ n - 1) := by
        push_cast; ring
      rw [this]
      exact Ideal.add_mem _ ih hp
  have hs : (∑ i ∈ Finset.range m, z ^ i) ≠ 0 := by
    intro h0
    apply hmI
    have := hdiff m
    rw [h0, zero_sub] at this
    simpa using (maximalIdeal V).neg_mem this
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hzm, sub_self]
  have hz0 : z - 1 = 0 := (mul_eq_zero.1 hprod).resolve_left hs
  have : z = 1 := sub_eq_zero.1 hz0
  have := congrArg (fun w : V => (w : F)) this
  simpa [hz] using this

theorem main : ∀ {F : Type} [inst : Field F] (V : ValuationSubring F) {m : ℕ},
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (↑m : F) = (1 : ValuationSubring.ValueGroup V) →
    ∀ {ζ : F}, ζ ^ m = (1 : F) →
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (ζ - (1 : F)) < (1 : ValuationSubring.ValueGroup V) →
    ζ = (1 : F) := by
  intro F _ V m hm ζ hζ h1
  exact eq_one_of_pow_eq_one V hm hζ h1

end GlobalTheory.RootOfUnityEqOne
