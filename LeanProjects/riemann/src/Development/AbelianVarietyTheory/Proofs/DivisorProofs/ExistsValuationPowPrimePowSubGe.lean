import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PowLim

theorem pow_prime_step {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ}
    (hp : p.Prime) (hvp : v (p : C) = 1) {a b : C} (ha : 0 ≤ v a) (hb : 0 ≤ v b) {t ε : ℝ}
    (hεt : ε ≤ t) (hε1 : ε ≤ 1) (ht : (t : WithTop ℝ) ≤ v (a - b)) :
    ((t + ε : ℝ) : WithTop ℝ) ≤ v (a ^ p - b ^ p) := by
  let R : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : 0 ≤ v a := ha
        have hb' : 0 ≤ v b := hb
        show 0 ≤ v (a * b)
        rw [v.map_mul]
        exact add_nonneg ha' hb'
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (v.map_add _ _)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]; exact le_top
      neg_mem' := fun {a} ha => by
        show 0 ≤ v (-a)
        rw [v.map_neg]; exact ha }
  have haR : a ∈ R := ha
  have hbR : b ∈ R := hb
  have hdR : a - b ∈ R := R.sub_mem haR hbR
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨a - b, hdR⟩ : R) ⟨b, hbR⟩
  have hr' := congrArg (fun z : R => (z : C)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
    sub_add_cancel] at hr'
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have e : a ^ p - b ^ p = (a - b) * (a - b) * (a - b) ^ k + (p : C) * (a - b) * (b * r) := by
    rw [hr']
    have : (a - b) ^ p = (a - b) * (a - b) * (a - b) ^ k := by rw [hk]; ring
    rw [this]; ring
  have h1 : (0 : WithTop ℝ) ≤ v ((a - b) ^ k) := R.pow_mem hdR k
  have h2 : (0 : WithTop ℝ) ≤ v (b * (r : C)) := R.mul_mem hbR r.2
  have hε : (ε : WithTop ℝ) ≤ v (a - b) := le_trans (WithTop.coe_le_coe.2 hεt) ht
  have hε1' : (ε : WithTop ℝ) ≤ 1 := by exact_mod_cast hε1
  rw [e]
  refine le_trans (le_min ?_ ?_) (v.map_add _ _)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add]
    exact le_trans (add_le_add ht hε) (le_add_of_nonneg_right h1)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add, hvp, add_comm (t : WithTop ℝ)]
    exact le_trans (add_le_add hε1' ht) (le_add_of_nonneg_right h2)

theorem pow_prime_pow_close : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  intro C _ v p hp hvp x y hx hy hxy r
  have hx' : 0 ≤ v x := hx
  have hy' : 0 ≤ v y := hy
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (ε : WithTop ℝ) ≤ v (x - y) := by
    generalize v (x - y) = w at hxy
    induction w using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, le_top⟩
    | coe s =>
      have hs : 0 < s := by exact_mod_cast hxy
      exact ⟨min s 1, lt_min hs one_pos, min_le_right _ _, WithTop.coe_le_coe.2 (min_le_left _ _)⟩
  have hpow : ∀ (z : C) (n : ℕ), 0 ≤ v z → 0 ≤ v (z ^ n) := by
    intro z n hz
    rw [v.map_pow]
    exact nsmul_nonneg hz n
  have key : ∀ N : ℕ, ((((N : ℝ) + 1) * ε : ℝ) : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
    intro N
    induction N with
    | zero => simpa using hε
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have := pow_prime_step v hp hvp (hpow x (p ^ N) hx') (hpow y (p ^ N) hy')
        (t := ((N : ℝ) + 1) * ε) (ε := ε) (by nlinarith) hε1 ih
      rw [← pow_mul, ← pow_mul, ← pow_succ] at this
      refine le_trans (WithTop.coe_le_coe.2 (le_of_eq ?_)) this
      push_cast; ring
  obtain ⟨M, hM⟩ := exists_nat_gt (r / ε)
  refine ⟨M, fun N hN => le_trans (WithTop.coe_le_coe.2 ?_) (key N)⟩
  have h1 : (M : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ hε0] at hM
  nlinarith

end GlobalTheory.PowLim
