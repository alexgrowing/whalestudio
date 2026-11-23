import Formalism.IncomingBounds.DefsThmP
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco

noncomputable section
open scoped BigOperators
open MvPowerSeries Finset

namespace Formalism.IncomingBounds

section ThmPExpLemmas

variable {C : Type} [Field C] {σ : Type}

theorem thmPExp_coeff_pow_eq_zero {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    {m : σ →₀ ℕ} {k : ℕ} (hk : m.degree < k) : coeff m (h ^ k) = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (le_order_pow_of_constantCoeff_eq_zero k hh))

theorem thmPExp_coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {m : σ →₀ ℕ} {j j' : ℕ} (hk : m.degree < j + j') :
    coeff m (a ^ j * b ^ j') = 0 :=
  by
  have h1 := le_order_pow_of_constantCoeff_eq_zero j ha
  have h2 := le_order_pow_of_constantCoeff_eq_zero j' hb
  apply coeff_of_lt_order
  calc ((m.degree : ℕ) : ℕ∞) < ((j + j' : ℕ) : ℕ∞) := by exact_mod_cast hk
    _ = (j : ℕ∞) + (j' : ℕ∞) := by push_cast; rfl
    _ ≤ (a ^ j).order + (b ^ j').order := add_le_add h1 h2
    _ ≤ _ := le_order_mul

theorem thmPExp_coeff_mvExp {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    (m : σ →₀ ℕ) {N : ℕ} (hN : m.degree < N) :
    coeff m (mvExp h) = ∑ k ∈ range N, coeff m (h ^ k) / (k.factorial : C) := by
  change ∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) = _
  apply Finset.sum_subset (range_subset_range.2 (by omega))
  intro k hk hk'
  simp only [mem_range, not_lt] at hk hk'
  rw [thmPExp_coeff_pow_eq_zero hh (by omega), zero_div]

theorem thmPExp_degree_le_of_mem_antidiagonal [DecidableEq σ] {m : σ →₀ ℕ} {pq : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hpq : pq ∈ antidiagonal m) : pq.1.degree ≤ m.degree ∧ pq.2.degree ≤ m.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have := congrArg Finsupp.degree hpq
  rw [map_add] at this
  omega

end ThmPExpLemmas

theorem thmPExp_choose_div_factorial {K : Type} [Field K] [CharZero K] {k j : ℕ} (hjk : j ≤ k) :
    ((k.choose j : ℕ) : K) / (k.factorial : K) =
      1 / ((j.factorial : K) * ((k - j).factorial : K)) := by
  have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hjk)
  push_cast at h
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hj : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkj : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff hk (mul_ne_zero hj hkj), one_mul, ← h]
  ring

theorem expSeriesAdd : ExpAdd := by
  intro K _ _ σ a b ha hb
  classical
  ext m
  have hN : m.degree < m.degree + 1 := Nat.lt_succ_self _
  set N := m.degree + 1 with hNdef
  have hab : constantCoeff (a + b) = 0 := by simp [ha, hb]
  have hmid : ∀ F : ℕ → ℕ → K,
      ∑ k ∈ range N, ∑ j ∈ range (k + 1), F j (k - j) =
        ∑ j ∈ range N, ∑ j' ∈ range (N - j), F j j' := by
    intro F
    rw [Finset.sum_comm' (t' := range N) (s' := fun j => Ico j N)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      congr 1
      omega
    · intro k j
      simp only [mem_range, mem_Ico]
      omega
  calc coeff m (mvExp (a + b))
      = ∑ k ∈ range N, coeff m ((a + b) ^ k) / (k.factorial : K) := thmPExp_coeff_mvExp hab m hN
    _ = ∑ k ∈ range N, ∑ j ∈ range (k + 1),
          coeff m (a ^ j * b ^ (k - j)) / ((j.factorial : K) * ((k - j).factorial : K)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [add_pow, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [mem_range] at hj
        rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C, mul_div_assoc,
          thmPExp_choose_div_factorial (by omega), mul_one_div]
    _ = ∑ j ∈ range N, ∑ j' ∈ range (N - j),
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) :=
        hmid (fun j j' => coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)))
    _ = ∑ j ∈ range N, ∑ j' ∈ range N,
          coeff m (a ^ j * b ^ j') / ((j.factorial : K) * (j'.factorial : K)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        apply Finset.sum_subset (range_subset_range.2 (by omega))
        intro j' _ hj'
        simp only [mem_range, not_lt] at hj'
        rw [thmPExp_coeff_pow_mul_pow_eq_zero ha hb (by omega), zero_div]
    _ = ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b) := by
        symm
        calc ∑ pq ∈ antidiagonal m, coeff pq.1 (mvExp a) * coeff pq.2 (mvExp b)
            = ∑ pq ∈ antidiagonal m, ∑ j ∈ range N, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := by
              refine Finset.sum_congr rfl (fun pq hpq => ?_)
              rw [thmPExp_coeff_mvExp ha pq.1 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).1; omega),
                thmPExp_coeff_mvExp hb pq.2 (N := N)
                  (by have := (thmPExp_degree_le_of_mem_antidiagonal hpq).2; omega),
                Finset.sum_mul_sum]
          _ = ∑ j ∈ range N, ∑ pq ∈ antidiagonal m, ∑ j' ∈ range N,
                (coeff pq.1 (a ^ j) / (j.factorial : K)) *
                  (coeff pq.2 (b ^ j') / (j'.factorial : K)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun j' _ => ?_)
              rw [coeff_mul, Finset.sum_div]
              refine Finset.sum_congr rfl (fun pq _ => ?_)
              rw [div_mul_div_comm]
    _ = coeff m (mvExp a * mvExp b) := (coeff_mul _ _ _).symm

theorem thmPExp_wt_le_add_iff (y : WithTop ℝ) (c w : ℝ) :
    ((c : ℝ) : WithTop ℝ) ≤ y + ((w : ℝ) : WithTop ℝ) ↔ ((c - w : ℝ) : WithTop ℝ) ≤ y := by
  induction y with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

theorem thmPExp_val_coeff_pow {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) {σ : Type}
    (w : (σ →₀ ℕ) → ℝ) (hw : ∀ m m', w (m + m') = w m + w m') (c : ℝ)
    (h : MvPowerSeries σ K) (hh : ∀ m, ((c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m h)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), (((k : ℝ) * c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m (h ^ k)) := by
  classical
  have hw0 : w 0 = 0 := by have := hw 0 0; simp at this; linarith
  intro k
  induction k with
  | zero =>
    intro m
    rw [pow_zero, coeff_one]
    split_ifs with hm
    · subst hm; simp [hw0]
    · simp
  | succ k ih =>
    intro m
    rw [pow_succ, coeff_mul]
    apply AddValuation.map_le_sum
    intro pq hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [AddValuation.map_mul, ← hpq, hw]
    calc ((((k + 1 : ℕ) : ℝ) * c - (w pq.1 + w pq.2) : ℝ) : WithTop ℝ)
        = (((k : ℝ) * c - w pq.1 : ℝ) : WithTop ℝ) + ((c - w pq.2 : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add (ih pq.1) (hh pq.2)

theorem expWeight_of (hV : ValNat) : ExpWeight := by
  intro K _ _ v l hl hvl hvp σ w hw h hh hwt m
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hpos : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have hc0 : (0:ℝ) < 1 / ((l:ℝ) - 1) := by positivity
  have hh' : ∀ m, ((1 / ((l:ℝ) - 1) - w m : ℝ) : WithTop ℝ) ≤ v (coeff m h) :=
    fun m => (thmPExp_wt_le_add_iff _ _ _).1 (hwt m)
  have hpow := thmPExp_val_coeff_pow v w hw _ h hh'
  rw [show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, thmPExp_wt_le_add_iff, zero_sub]
  change _ ≤ v (∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : K))
  apply AddValuation.map_le_sum
  intro k _
  have hfk := hV K v l hl hvl hvp k.factorial (Nat.factorial_ne_zero k)
  have hkne : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hdiv : v (coeff m (h ^ k) / (k.factorial : K)) + v (k.factorial : K) =
      v (coeff m (h ^ k)) := by
    rw [← AddValuation.map_mul, div_mul_cancel₀ _ hkne]
  rw [hfk] at hdiv
  have hbound : (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) * (1 / ((l:ℝ) - 1)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · calc (padicValNat l k.factorial : ℝ) ≤ ((k:ℝ) - 1) / ((l:ℝ) - 1) :=
            (padicValFactorialBounds l hl k hk).2
        _ ≤ (k : ℝ) * (1 / ((l:ℝ) - 1)) := by
            rw [mul_one_div]; gcongr; linarith
  have hlow := hpow k m
  rw [← hdiv, thmPExp_wt_le_add_iff] at hlow
  exact le_trans (WithTop.coe_le_coe.2 (by linarith)) hlow

theorem thmPExp_valNat : ValNat := by
  intro K _ _ v l hl hvl hvp N hN
  have := Fact.mk hl
  induction N using Nat.recOnMul with
  | zero => exact absurd rfl hN
  | one => simp
  | prime p hp =>
    by_cases hpl : p = l
    · subst hpl; rw [hvl, padicValNat_self]; simp
    · have := Fact.mk hp
      rw [hvp p hp hpl, padicValNat_primes (Ne.symm hpl)]; simp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun h => hN (by simp [h])
    have hb0 : b ≠ 0 := fun h => hN (by simp [h])
    rw [Nat.cast_mul, AddValuation.map_mul, ha ha0, hb hb0, padicValNat.mul ha0 hb0]
    push_cast
    rfl

theorem expSeriesWeight : ExpWeight := expWeight_of thmPExp_valNat

theorem valuationNatCast : ValNat := thmPExp_valNat

end Formalism.IncomingBounds
