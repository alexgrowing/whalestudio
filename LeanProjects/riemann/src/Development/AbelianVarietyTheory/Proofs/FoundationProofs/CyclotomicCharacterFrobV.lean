import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem rootOfUnity_eq_one_of_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {m : ℕ} (hm : ¬ v (m : K) < 1) {η : K} (hη : η ^ m = 1) (h1 : v (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hm
  have hv : v η = 1 := by
    have := v.map_one_add_of_lt h1
    simpa using this
  have hi : ∀ i : ℕ, v (1 - η ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - η ^ (i + 1) = (1 - η ^ i) + -(η ^ i * (η - 1)) := by ring
      rw [e]
      refine v.map_add_lt ih ?_
      rw [v.map_neg, map_mul, map_pow, hv, one_pow, one_mul]
      exact h1
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have e : (m : K) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact v.map_sum_lt one_ne_zero fun i _ => hi i

theorem not_val_lt_one_of_coprime {K : Type*} [Field K] (V : ValuationSubring K) {m q : ℕ} (h : Nat.Coprime m q)
    (hq : V.valuation (q : K) < 1) : ¬ V.valuation (m : K) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : (1 : K) = (a : K) * m + (b : K) * q := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hz : ∀ (c : ℤ) (x : K), V.valuation x < 1 → V.valuation ((c : K) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    have hc : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (intCast_mem V c)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx
  have := V.valuation.map_add_lt (hz a _ hm) (hz b _ hq)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem FrobV.apply_rootOfUnity {Ω : Type} [Field Ω] [Algebra ℚ Ω] {V : ValuationSubring Ω} {q : ℕ}
    {s : Ω ≃ₐ[ℚ] Ω} (hs : FrobV V q s) {m : ℕ} (hm0 : m ≠ 0) (hm : Nat.Coprime m q) {ζ : Ω} (hζ : ζ ^ m = 1) :
    s ζ = ζ ^ q := by
  have hq : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.mp hs.1
  have hv : V.valuation ζ = 1 := by
    have := congrArg V.valuation hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_left hm0).mp this
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : ζ ∈ V := (V.valuation_le_one_iff _).mp hv.le
  have h := (hs.2 ζ hV).2.2
  have hq0 : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : s ζ / ζ ^ q = 1 := by
    refine rootOfUnity_eq_one_of_val V.valuation (not_val_lt_one_of_coprime V hm hq) ?_ ?_
    · rw [div_pow, ← map_pow, hζ, map_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
    · rw [div_sub_one hq0, map_div₀, map_pow, hv, one_pow, div_one]
      exact h
  exact (div_eq_one_iff_eq hq0).mp key

theorem cyclotomicCharacter_frobV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l q : ℕ) [Fact l.Prime],
    q.Prime → q ≠ l → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q := by
  intro Ω _ _ _ l q hl hq hql V s hs
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, NeZero ((l ^ i : ℕ) : Ω) := fun i => ⟨by exact_mod_cast pow_ne_zero i hl.out.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ (l ^ n) = 1 := (mem_rootsOfUnity' _ _).mp ht
  have hc : Nat.Coprime (l ^ n) q := ((Nat.coprime_primes hl.out hq).mpr hql.symm).pow_left n
  have := hs.apply_rootOfUnity (pow_ne_zero n hl.out.ne_zero) hc ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod q ht']
  exact this

end GlobalTheory.KZ.ES
