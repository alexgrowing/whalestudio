import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglogStatement

open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.SumBound

open Finset

theorem sum_log_le (M : ℕ) :
    ∑ p ∈ (range (M + 1)).filter Nat.Prime, Real.log p ≤ M * Real.log 4 := by
  have h := primorial_le_4_pow M
  unfold primorial at h
  have h' : (∏ p ∈ (range (M + 1)).filter Nat.Prime, (p:ℝ)) ≤ (4:ℝ) ^ M := by
    rw [← Nat.cast_prod]
    exact_mod_cast h
  have hpos : ∀ p ∈ (range (M + 1)).filter Nat.Prime, (0:ℝ) < (p:ℝ) := by
    intro p hp
    have := (mem_filter.1 hp).2.pos
    positivity
  have := Real.log_le_log (Finset.prod_pos hpos) h'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at this
  simpa [Real.log_pow] using this

theorem eOf_nonneg (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (p : ℕ) (hp : p.Prime) : 0 ≤ eOf F N k m Mb Sm vd M S₀ R p := by
  have hv := hvd p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  unfold eOf eSmall
  split_ifs with h1 h2 h3 h4
  · exact le_rfl
  · positivity
  · positivity
  · have hM : (1:ℝ) ≤ M := by
      have : 2 ≤ M := le_trans hp.two_le (not_lt.1 h1)
      exact_mod_cast (show 1 ≤ M by omega)
    have hl : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) hM
    positivity
  · positivity

theorem point_le (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ : ℝ) (S₀ R : Finset ℕ) (hMb : 0 ≤ Mb) (hSm : 0 ≤ Sm)
    (hvd : ∀ q, 0 ≤ vd q) (hLg : 1 ≤ large₂) (hLM : Real.log M ≤ large₂)
    (hRq : ∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) (p : ℕ) (hp : p.Prime) (hpM : p ≤ M) :
    eOf F N k m Mb Sm vd M S₀ R p * Real.log p ≤
      (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) + (if p ∈ R then (F * m * Mb + Sm) * large₂ else 0)
      + (6 * F * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) + Real.log p
      + (if m * p < k then F * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlp1 : Real.log p ≤ (p:ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < p by linarith); linarith
  have ht0 : 0 ≤ Real.log p / ((p:ℝ) - 1) := div_nonneg hlp.le hp1.le
  have ht1 : Real.log p / ((p:ℝ) - 1) ≤ 1 := (div_le_one hp1).2 hlp1
  have hMr : (p:ℝ) ≤ M := by exact_mod_cast hpM
  have hlpM : Real.log p ≤ Real.log M := Real.log_le_log (by linarith) hMr
  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  have hinv : 0 ≤ 1 / ((p:ℝ) - 1) := by positivity
  have hv := hvd p
  have hI2 : 0 ≤ (if p ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hIR : 0 ≤ (if p ∈ R then ((F:ℝ) * m * Mb + Sm) * large₂ else 0) := by split_ifs <;> linarith
  have hIk : 0 ≤ (if m * p < k then (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1))
      + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂ else 0) := by
    split_ifs
    · have h1 : 0 ≤ (F:ℝ) * m * Mb * large₂ / 2 * (1 / ((p : ℝ) - 1)) :=
        mul_nonneg (div_nonneg (mul_nonneg hX (by linarith)) (by norm_num)) hinv
      have h2 : 0 ≤ 2 * (F:ℝ) * (m + 1) * (N : ℝ) ^ 2 * large₂ :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    · exact le_rfl
  have hB : 0 ≤ (6 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p : ℝ) - 1)) :=
    mul_nonneg (by positivity) ht0
  have hXt : 0 ≤ (F:ℝ) * m * Mb * (Real.log p / ((p : ℝ) - 1)) := mul_nonneg hX ht0
  have hnM : ¬ M < p := by omega
  unfold eOf
  rw [if_neg hnM]
  by_cases h2 : p ∈ S₀
  · rw [if_pos h2, if_pos h2]
    have e : ((F:ℝ) * m * Mb + Sm) * ((1 + vd p / 2) * Real.log p) = ((F:ℝ) * m * (1 + vd p / 2) * Mb + Sm) * Real.log p + Sm * (vd p / 2 * Real.log p) := by ring
    have e0 : 0 ≤ Sm * (vd p / 2 * Real.log p) := by positivity
    linarith
  · rw [if_neg h2]
    by_cases hR : p ∈ R
    · rw [if_pos hR]
      simp only [h2, hR, ↓reduceIte] at hI2 hIR ⊢
      have e : ((F:ℝ) * N * Mb + Sm) / ((p:ℝ) - 1) * Real.log p
          = F * Mb * (N * Real.log p / ((p:ℝ) - 1)) + Sm * (Real.log p / ((p:ℝ) - 1)) := by ring
      rw [e]
      have f1 : (F:ℝ) * Mb * (N * Real.log p / ((p:ℝ) - 1)) ≤ F * Mb * (m * large₂) :=
        mul_le_mul_of_nonneg_left (hRq p hR) (by positivity)
      have f2 : Sm * (Real.log p / ((p:ℝ) - 1)) ≤ Sm * large₂ := by nlinarith
      nlinarith
    · rw [if_neg hR]
      simp only [h2, hR, ↓reduceIte, add_zero, zero_add] at hI2 hIR ⊢
      by_cases hk : m * p < k
      · rw [if_pos hk, if_pos hk]
        unfold eSmall
        have hlb : Real.logb p M * Real.log p = Real.log M := by
          rw [Real.logb, div_mul_cancel₀ _ hlp.ne']
        have e : (((F:ℝ) * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p:ℝ) - 1)
            + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M + 1) + 1) * Real.log p
            = (4 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
              + F * m * Mb / 2 * (Real.logb p M * Real.log p) * (1 / ((p:ℝ) - 1))
              + F * (m + 1) * (N:ℝ) ^ 2 * (Real.logb p M * Real.log p + Real.log p) + Real.log p := by ring
        rw [e, hlb]
        have g1 : (F:ℝ) * m * Mb / 2 * Real.log M * (1 / ((p:ℝ) - 1))
            ≤ F * m * Mb * large₂ / 2 * (1 / ((p:ℝ) - 1)) := by
          have : (F:ℝ) * m * Mb / 2 * Real.log M ≤ F * m * Mb * large₂ / 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hinv
        have hQ : 0 ≤ (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 := by positivity
        have g2 : (F:ℝ) * (m + 1) * (N:ℝ) ^ 2 * (Real.log M + Real.log p)
            ≤ F * (m + 1) * (N:ℝ) ^ 2 * (2 * large₂) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
        have g0 : (4 * (F:ℝ) * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1))
            ≤ (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) ht0
        linarith
      · rw [if_neg hk, if_neg hk]
        have e : ((6 * (F:ℝ) * m * Mb + Sm) / ((p:ℝ) - 1) + 1) * Real.log p
            = (6 * F * m * Mb + Sm) * (Real.log p / ((p:ℝ) - 1)) + Real.log p := by ring
        rw [e]
        linarith

end GlobalTheory.SumBound

namespace GlobalTheory.SumBound

open Finset

theorem sum_ite_const (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    ∑ q ∈ s, (if P q then c else 0) = (s.filter P).card * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem primeSum_eOf : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) →
    N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ →
    Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) →
    PrimeSum ((Finset.range (M + 1)).filter Nat.Prime)
      (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0)
      (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  intro F N k m M Mb Sm vd large₂ ll S₀ R hMb hSm hvd hNk hmk hm1 hLg hll hLM hLN hvdL hllk hRc hRq
  set S := (Finset.range (M + 1)).filter Nat.Prime with hS
  refine ⟨fun q hq => (mem_filter.1 hq).2, fun q => ?_, fun q hq => ?_, ?_⟩
  · beta_reduce
    split_ifs with h
    · exact eOf_nonneg F N k m Mb Sm vd M S₀ R hMb hSm hvd q h
    · exact le_rfl
  · beta_reduce
    split_ifs with h
    · have hqM : M < q := by
        by_contra hc
        exact hq (mem_filter.2 ⟨mem_range.2 (by omega), h⟩)
      unfold eOf; rw [if_pos hqM]
    · rfl

  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hMn : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hX : 0 ≤ (F:ℝ) * m * Mb := by positivity
  have hA : 0 ≤ ((F:ℝ) * m * Mb + Sm) * large₂ := by nlinarith
  set A := ((F:ℝ) * m * Mb + Sm) * large₂ with hAdef
  set K := S.filter (fun q => m * q < k) with hK
  have step1 : ∑ q ∈ S, (if q.Prime then eOf F N k m Mb Sm vd M S₀ R q else 0) * Real.log q ≤
      ∑ q ∈ S, ((if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) + (if q ∈ R then A else 0)
      + (6 * F * m * Mb + Sm) * (Real.log q / ((q : ℝ) - 1)) + Real.log q
      + (if m * q < k then F * m * Mb * large₂ / 2 * (1 / ((q : ℝ) - 1)) + 2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂
          else 0)) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqp := (mem_filter.1 hq).2
    have hqM : q ≤ M := by have := mem_range.1 (mem_filter.1 hq).1; omega
    rw [if_pos hqp]
    exact point_le F N k m M Mb Sm vd large₂ S₀ R hMb hSm hvd hLg hLM hRq q hqp hqM
  simp only [Finset.sum_add_distrib] at step1
  have t4 : ∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0) ≤ 3 / 2 * A := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have h1 : ∑ q ∈ S.filter (fun q => q ∈ S₀), (1 + vd q / 2) * Real.log q ≤ ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2) fun q _ _ =>
        mul_nonneg (by have := hvd q; positivity) (Real.log_natCast_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hvdL) (show 0 ≤ (F:ℝ) * m * Mb + Sm by positivity)
    rw [hAdef]; linarith
  generalize (∑ q ∈ S, (if q ∈ S₀ then ((F:ℝ) * m * Mb + Sm) * ((1 + vd q / 2) * Real.log q) else 0)) = W₀ at step1 t4
  rw [sum_ite_const, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at step1

  have cR : ((S.filter (fun q => q ∈ R)).card : ℝ) ≤ 2 := by
    have : (S.filter (fun q => q ∈ R)).card ≤ R.card :=
      Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)
    exact_mod_cast this.trans hRc
  have hmert : ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) ≤ Real.log M + 2.2 :=
    GlobalTheory.PrimeLogSum.sum_log_div_pred_le M
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hth : ∑ q ∈ S, Real.log q ≤ 3 * M := by
    have := sum_log_le M
    have h2 : (M:ℝ) * Real.log 4 ≤ M * 3 := mul_le_mul_of_nonneg_left hlog4 hMn
    linarith
  have hKS : ∀ q ∈ K, q.Prime ∧ m * q < k := fun q hq =>
    ⟨(mem_filter.1 (mem_filter.1 hq).1).2, (mem_filter.1 hq).2⟩
  have hrec : ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ 13 * ll := by
    by_cases hk3 : 3 ≤ k
    · have sub : K ⊆ (Finset.range (k + 1)).filter Nat.Prime := by
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        refine mem_filter.2 ⟨mem_range.2 ?_, hp⟩
        have : q ≤ m * q := Nat.le_mul_of_pos_left q (by omega)
        omega
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => 1 / ((q : ℝ) - 1)) sub (fun q hq _ => by
        have : (2:ℝ) ≤ q := by exact_mod_cast (mem_filter.1 hq).2.two_le
        have : (0:ℝ) < (q:ℝ) - 1 := by linarith
        positivity)
      have h2 := GlobalTheory.T.sum_primes_inv_pred_le_loglog k hk3
      linarith
    · have : K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        obtain ⟨hp, hqk⟩ := hKS q hq
        have : 2 ≤ m * q := le_trans hp.two_le (Nat.le_mul_of_pos_left q (by omega))
        omega
      rw [this, Finset.sum_empty]; linarith
  have hcard : (K.card : ℝ) * ((m:ℝ) + 1) ≤ 2 * N := by
    have sub : K ⊆ Finset.Icc 1 ((k - 1) / m) := by
      intro q hq
      obtain ⟨hp, hqk⟩ := hKS q hq
      refine Finset.mem_Icc.2 ⟨hp.one_lt.le, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.mul_comm]; omega
    have h1 : K.card ≤ (k - 1) / m := by
      have := Finset.card_le_card sub
      simpa using this
    have h2 : K.card * m ≤ k - 1 := le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self _ _)
    have h3 : K.card ≤ K.card * m := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : K.card * (m + 1) ≤ 2 * N := by rw [Nat.mul_succ]; omega
    exact_mod_cast h4

  have hLg0 : (0:ℝ) ≤ large₂ := by linarith
  have hll0 : (0:ℝ) ≤ ll := by linarith
  have t1 : (6 * (F:ℝ) * m * Mb + Sm) * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)
      ≤ (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : (F:ℝ) * m * Mb * large₂ / 2 * ∑ q ∈ K, 1 / ((q : ℝ) - 1) ≤ (F:ℝ) * m * Mb * large₂ / 2 * (13 * ll) :=
    mul_le_mul_of_nonneg_left hrec (by positivity)
  have t3 : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂) ≤ 2 * F * (N:ℝ) ^ 2 * large₂ * (2 * N) := by
    have e : (K.card : ℝ) * (2 * F * (m + 1) * (N : ℝ) ^ 2 * large₂)
        = 2 * F * (N:ℝ) ^ 2 * large₂ * ((K.card : ℝ) * ((m:ℝ) + 1)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hcard (by positivity)
  have t5 : ((S.filter (fun q => q ∈ R)).card : ℝ) * A ≤ 2 * A := mul_le_mul_of_nonneg_right cR hA
  have t6 : A ≤ A * ll := le_mul_of_one_le_right hA hll
  have hSL : 0 ≤ Sm * large₂ := mul_nonneg hSm hLg0
  have t7 : (F:ℝ) * m * Mb * large₂ ≤ A := by rw [hAdef]; linarith
  have t8 : (F:ℝ) * m * Mb * large₂ * ll ≤ A * ll := mul_le_mul_of_nonneg_right t7 hll0
  have t9 : (6 * (F:ℝ) * m * Mb + Sm) * (3.2 * large₂) ≤ 96 / 5 * A := by rw [hAdef]; norm_num; linarith
  have t10 : 0 ≤ (F:ℝ) * (N:ℝ) ^ 3 * large₂ := by positivity
  clear_value A
  linarith

end GlobalTheory.SumBound
