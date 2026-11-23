import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimePowerVonMangoldtSumBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumVonMangoldtDivSqIocLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumVonMangoldtDivSqTail
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumDivSubLeTwoLogOfPartialSums

open Finset ArithmeticFunction

namespace GlobalTheory

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem meanSq_cn_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cn x n :=
  mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem meanSq_cn_eq_zero (x : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) : cn x n = 0 := by
  unfold cn
  rw [vonMangoldt_eq_zero_iff.2 hn, zero_mul]

theorem meanSq_fiber_le {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (if n.minFac = p then cn x n else 0) ≤ sP x p := by
  classical
  unfold sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  rw [← Finset.sum_image (s := (Icc 1 N).filter (fun i => p ^ i ≤ N)) (g := fun i => p ^ i)
    (f := fun n => cn x n) (fun a _ b _ h => Nat.pow_right_injective hp.two_le h)]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter_of_ne (p := fun n => IsPrimePow n)
    (fun n _ h => by by_contra h'; exact h (meanSq_cn_eq_zero x h'))]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => meanSq_cn_nonneg hx n)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
  obtain ⟨p', i, hp', hi, rfl⟩ := (isPrimePow_nat_iff _).1 h4
  rw [hp'.pow_minFac hi.ne'] at h3
  subst h3
  refine Finset.mem_image.2 ⟨i, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hi, (Nat.lt_pow_self hp.one_lt).le.trans h2⟩, h2⟩

theorem meanSq_expand (I PPs : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ) (hκ : ∀ n, ‖κ n‖ ≤ 1) :
    (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) / PPs.card ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
  have h1 : ((∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n * c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [jacobiSym.mul_left]
    simp only [map_mul, Complex.conj_ofReal, map_intCast]
    push_cast
    ring
  have h2 : (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc n) (hc n'))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_of_le_one_right (mul_nonneg (hc n) (hc n'))
      (mul_le_one₀ (hκ n) (norm_nonneg _) (hκ n'))
  refine (div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)).trans (le_of_eq ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [abs_div, Nat.abs_cast, mul_div_assoc]

theorem meanSq_abs_mean_le_one (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by
  rw [abs_div, Nat.abs_cast]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy a q with h | h | h <;> simp [h]
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem meanSq_primeFactors_outPart (m₀ m : ℕ) :
    (outPart m₀ m).primeFactors = m.primeFactors.filter (fun p => ¬ p ∣ m₀ ∧ Odd (m.factorization p)) := by
  unfold outPart
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1

theorem meanSq_card_primeFactors_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    (outPart m₀ (n * n')).primeFactors.card ≤ 2 := by
  rw [meanSq_primeFactors_outPart]
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.primeFactors_mul hn.ne_zero hn'.ne_zero]
  refine (Finset.card_union_le _ _).trans ?_
  rw [isPrimePow_iff_card_primeFactors_eq_one.1 hn, isPrimePow_iff_card_primeFactors_eq_one.1 hn']

theorem meanSq_mem_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (hne : n.minFac ≠ n'.minFac) (hsq : ¬ IsSquare n) (hm : ¬ n.minFac ∣ m₀) :
    n.minFac ∈ (outPart m₀ (n * n')).primeFactors := by
  obtain ⟨p, i, hp, hi, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  obtain ⟨p', j, hp', hj, rfl⟩ := (isPrimePow_nat_iff _).1 hn'
  rw [hp.pow_minFac hi.ne'] at hne hm ⊢
  rw [hp'.pow_minFac hj.ne'] at hne
  rw [meanSq_primeFactors_outPart, Finset.mem_filter]
  refine ⟨Nat.mem_primeFactors.2 ⟨hp, Dvd.dvd.mul_right (dvd_pow_self p hi.ne') _,
    mul_ne_zero hn.ne_zero hn'.ne_zero⟩, hm, ?_⟩
  rw [Nat.factorization_mul hn.ne_zero hn'.ne_zero, hp.factorization_pow, hp'.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, add_zero]
  rw [← Nat.not_even_iff_odd]
  exact fun h => hsq (h.isSquare_pow p)

theorem meanSq_pairs {x : ℝ} (hx : 0 ≤ x) (m₀ : ℕ) (hm₀ : 0 < m₀) (nStar : ℕ) (A : ℕ → ℕ → ℝ) (η S : ℝ)
    (hη : 0 ≤ η) (hS0 : 0 ≤ S) (hS : ∀ p : ℕ, p.Prime → sP x p ≤ S) (hA1 : ∀ n n', A n n' ≤ 1)
    (hA : ∀ n n' : ℕ, n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ → n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ →
      IsPrimePow n → IsPrimePow n' → outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → A n n' ≤ η) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, ∑ n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n * cn x n' * A n n' ≤
      η * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 +
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 +
      (Rsum x m₀ + 2 * S) ^ 2 := by
  classical
  have hfib := fun p hp => meanSq_fiber_le (p := p) hx hp
  have hc := meanSq_cn_nonneg hx
  unfold Rsum
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hN
  set f : ℕ → ℕ → ℝ := fun p n => if n.minFac = p then cn x n else 0 with hf
  have hf0 : ∀ p n, 0 ≤ f p n := fun p n => by
    simp only [hf]; split_ifs
    exacts [hc n, le_rfl]
  set P := (Icc 1 N).filter (fun p => p.Prime) with hP
  set M := m₀.primeFactors.filter (fun p => p ≤ N) with hM
  set T : Finset ℕ := if nStar.primeFactors.card ≤ 2 then nStar.primeFactors else ∅ with hT
  have hTcard : T.card ≤ 2 := by
    simp only [hT]; split_ifs with h
    exacts [h, by simp]
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    simp only [hT] at hp; split_ifs at hp with h
    exacts [Nat.prime_of_mem_primeFactors hp, absurd hp (Finset.notMem_empty p)]
  set U : ℕ → ℝ := fun n => (if IsSquare n then cn x n else 0) + ∑ p ∈ M, f p n + ∑ p ∈ T, f p n with hU
  have hU1 : ∀ n, 0 ≤ (if IsSquare n then cn x n else 0) := fun n => by
    split_ifs
    exacts [hc n, le_rfl]
  have hU2 : ∀ (B : Finset ℕ) n, 0 ≤ ∑ p ∈ B, f p n := fun B n => Finset.sum_nonneg fun p _ => hf0 p n
  have hU0 : ∀ n, 0 ≤ U n := fun n => add_nonneg (add_nonneg (hU1 n) (hU2 M n)) (hU2 T n)
  have hsingle : ∀ (B : Finset ℕ) (n : ℕ), n.minFac ∈ B → cn x n ≤ ∑ p ∈ B, f p n := by
    intro B n h
    have := Finset.single_le_sum (f := fun p => f p n) (fun p _ => hf0 p n) h
    simpa [hf] using this
  have hUc : ∀ n n' : ℕ, n ∈ Icc 1 N → IsPrimePow n → IsPrimePow n' → n.minFac ≠ n'.minFac →
      (outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar) → cn x n ≤ U n := by
    intro n n' hn hpn hpn' hne ho
    have a1 := hU1 n
    have a2 := hU2 M n
    have a3 := hU2 T n
    simp only [hU]
    by_cases hsq : IsSquare n
    · rw [if_pos hsq]; linarith
    by_cases hm : n.minFac ∣ m₀
    · have : n.minFac ∈ M := Finset.mem_filter.2
        ⟨Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hpn.ne_one, hm, hm₀.ne'⟩,
          (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩
      have := hsingle M n this
      linarith
    have h1 := meanSq_mem_outPart m₀ hpn hpn' hne hsq hm
    have h2 := meanSq_card_primeFactors_outPart m₀ hpn hpn'
    rcases ho with ho | ho
    · rw [ho] at h1; simp at h1
    · rw [ho] at h1 h2
      have : n.minFac ∈ T := by simp only [hT]; rw [if_pos h2]; exact h1
      have := hsingle T n this
      linarith
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, cn x n * cn x n' * A n n' ≤
      η * (cn x n * cn x n') + ∑ p ∈ P, f p n * f p n' + U n * U n' := by
    intro n hn n' hn'
    have b1 : 0 ≤ η * (cn x n * cn x n') := mul_nonneg hη (mul_nonneg (hc n) (hc n'))
    have b2 : 0 ≤ ∑ p ∈ P, f p n * f p n' := Finset.sum_nonneg fun p _ => mul_nonneg (hf0 p n) (hf0 p n')
    have b3 : 0 ≤ U n * U n' := mul_nonneg (hU0 n) (hU0 n')
    have b4 : cn x n * cn x n' * A n n' ≤ cn x n * cn x n' :=
      mul_le_of_le_one_right (mul_nonneg (hc n) (hc n')) (hA1 n n')
    by_cases hpn : IsPrimePow n
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn]; ring
      linarith
    by_cases hpn' : IsPrimePow n'
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn']; ring
      linarith
    by_cases hne : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 ⟨Nat.minFac_pos n, (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩,
          Nat.minFac_prime hpn.ne_one⟩
      have := Finset.single_le_sum (f := fun p => f p n * f p n')
        (fun p _ => mul_nonneg (hf0 p n) (hf0 p n')) hmem
      have e : f n.minFac n * f n.minFac n' = cn x n * cn x n' := by
        simp only [hf]; rw [if_pos trivial, if_pos hne.symm]
      simp only [e] at this
      linarith
    by_cases ho : outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar
    · have c1 := hUc n n' hn hpn hpn' hne ho
      have c2 := hUc n' n hn' hpn' hpn (Ne.symm hne) (by rwa [mul_comm n' n])
      have := mul_le_mul c1 c2 (hc n') (hU0 n)
      linarith
    · rw [not_or] at ho
      have := mul_le_mul_of_nonneg_left (hA n n' hn hn' hpn hpn' ho.1 ho.2) (mul_nonneg (hc n) (hc n'))
      linarith
  refine (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn').trans ?_
  simp_rw [Finset.sum_add_distrib]
  refine add_le_add (add_le_add (le_of_eq ?_) ?_) ?_
  · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  · have : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, f p n * f p n' =
        ∑ p ∈ P, (∑ n ∈ Icc 1 N, f p n) ^ 2 := by
      simp_rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm (s := P)]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_comm
    rw [this]
    refine Finset.sum_le_sum fun p hp => ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hf0 p n) (hfib p (Finset.mem_filter.1 hp).2) 2
  · rw [← Finset.sum_mul_sum, ← sq]
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hU0 n) ?_ 2
    simp only [hU]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter,
      Finset.sum_comm (t := M), Finset.sum_comm (t := T)]
    refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun p hp =>
      hfib p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1))) ?_
    have h1 : ∑ p ∈ T, ∑ n ∈ Icc 1 N, f p n ≤ T.card • S :=
      Finset.sum_le_card_nsmul _ _ _ fun p hp => (hfib p (hTprime p hp)).trans (hS p (hTprime p hp))
    rw [nsmul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hS0)
    exact_mod_cast hTcard

theorem meanSq_core : Formalism.HermitianLattices.GL2PrimeSums.JacobiTwistedMeanSquareBound := by
  intro hψ ε hε hε1 C' c' hC' hc'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.chebyshev_coefficient_sum_bound hψ
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.prime_sum_square_bound hψ
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.remainder_smooth_rough_bound hψ
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.prime_power_von_mangoldt_sum_bound
  refine ⟨max (Real.exp 1) (Real.exp (2 / c')), C' * C₁ ^ 2 + C₂ + (5 * |C₃| + 4 * |C₄|) ^ 2, ?_⟩
  intro x hx m₀ PPs κ nStar _ hm₀ hpr _ _ _ _ hκ hμ
  have hxe : Real.exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hL2 : 2 / c' ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 ((le_max_right _ _).trans hx)
  have hL0 : 0 ≤ Real.log x := by linarith
  have h1 := meanSq_expand (Icc 1 ⌊x ^ (400 : ℝ)⌋₊) PPs (cn x) (meanSq_cn_nonneg hx0.le) κ hκ
  have h2 := meanSq_pairs hx0.le m₀ hm₀ nStar
    (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)
    (C' * Real.exp (-c' * Real.log x ^ 2)) (|C₄| * Real.log x) (by positivity) (by positivity)
    (fun p hp => (hC₄ x hx2 p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hL0))
    (fun n n' => meanSq_abs_mean_le_one PPs _) hμ
  unfold sqSum
  refine (h1.trans h2).trans ?_
  have e1 : C' * Real.exp (-c' * Real.log x ^ 2) * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤
      C' * C₁ ^ 2 * x * Real.log x := by
    have s1 : (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤ (C₁ * x * Real.log x) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n) (hC₁ x hx2) 2
    have s2 : Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x) ≤ 1 := by
      have t1 : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      have t2 : 2 ≤ c' * Real.log x := by rw [div_le_iff₀ hc'] at hL2; linarith
      have t3 : x * x = Real.exp (2 * Real.log x) := by
        rw [two_mul, Real.exp_add, Real.exp_log hx0]
      calc Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)
          ≤ Real.exp (-c' * Real.log x ^ 2) * (x * x) := by gcongr
        _ = Real.exp (-c' * Real.log x ^ 2 + 2 * Real.log x) := by rw [t3, Real.exp_add]
        _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [mul_le_mul_of_nonneg_right t2 hL0]
    calc _ ≤ C' * Real.exp (-c' * Real.log x ^ 2) * (C₁ * x * Real.log x) ^ 2 := by gcongr
      _ = (C' * C₁ ^ 2 * x * Real.log x) * (Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) s2
  have e2 := hC₂ x hx2
  have e3 : (Rsum x m₀ + 2 * (|C₄| * Real.log x)) ^ 2 ≤ (5 * |C₃| + 4 * |C₄|) ^ 2 * x * Real.log x := by
    have r0 : 0 ≤ Rsum x m₀ := by
      unfold Rsum sP
      exact add_nonneg (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n)
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => meanSq_cn_nonneg hx0.le _)
    have r1 := hC₃ ε hε hε1 x hx2 m₀ hm₀ hpr
    have r2 : Real.log x ≤ x ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r3 : Real.log x ≤ x ^ ((1 : ℝ) / 4) / (1 / 4) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r4 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have r5 : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    have r6 : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      rw [sq, ← Real.rpow_add hx0]; norm_num
    have r7 : x ^ (ε / 5) * Real.log x ≤ 4 * x ^ ((1 : ℝ) / 2) := by
      have := mul_le_mul r4 r3 hL0 (by positivity)
      rw [← r5]; linarith
    have r8 : Rsum x m₀ ≤ |C₃| * (5 * x ^ ((1 : ℝ) / 2)) := by
      refine r1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have r9 : |C₄| * Real.log x ≤ |C₄| * (2 * x ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    calc _ ≤ ((5 * |C₃| + 4 * |C₄|) * x ^ ((1 : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = (5 * |C₃| + 4 * |C₄|) ^ 2 * x := by rw [mul_pow, r6]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1
  linarith

end GlobalTheory
