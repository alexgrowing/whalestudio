import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EnormSqLeLintegralDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.SpacedDetected

noncomputable def poly (Q : ℕ) (c : ℕ → ℂ) (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), c n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-s)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem succ_le_mul_pow_rpow_of_two_le (ε : ℝ) (hε : 0 < ε) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ≤ max 1 (1 / (ε * Real.log 2)) * ((p : ℝ) ^ a) ^ ε ∧
      ((2 : ℝ) ^ (1 / ε) ≤ p → ((a : ℝ) + 1) ≤ ((p : ℝ) ^ a) ^ ε) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have key : ((p : ℝ) ^ a) ^ ε = Real.exp (a * ε * Real.log p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.rpow_def_of_pos hp0]; ring_nf
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log two_pos hp'
  constructor
  · rw [key]
    have h1 : 1 + a * ε * Real.log 2 ≤ Real.exp (a * ε * Real.log p) := by
      have := Real.add_one_le_exp (a * ε * Real.log p)
      have : a * ε * Real.log 2 ≤ a * ε * Real.log p :=
        mul_le_mul_of_nonneg_left hlogp (by positivity)
      linarith
    set M := max 1 (1 / (ε * Real.log 2))
    have hM1 : 1 ≤ M := le_max_left _ _
    have hM2 : 1 / (ε * Real.log 2) ≤ M := le_max_right _ _
    have hMa : (a : ℝ) ≤ M * (a * ε * Real.log 2) := by
      have hpos : 0 < ε * Real.log 2 := by positivity
      have h0 : (0 : ℝ) ≤ a * ε * Real.log 2 := by positivity
      calc (a : ℝ) = 1 / (ε * Real.log 2) * (a * ε * Real.log 2) := by field_simp
        _ ≤ M * (a * ε * Real.log 2) := mul_le_mul_of_nonneg_right hM2 h0
    nlinarith
  · intro hbig
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hbig hε.le
    have : ((p : ℝ) ^ a) ^ ε = ((p : ℝ) ^ ε) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le, mul_comm]
    rw [this]
    calc ((a : ℝ) + 1) ≤ 2 ^ a := by
          have := Nat.lt_two_pow_self (n := a)
          exact_mod_cast this
      _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h2 a

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem exists_card_divisors_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ε := by
  set M := max 1 (1 / (ε * Real.log 2)) with hM
  set B := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨M ^ B, by positivity, fun n hn => ?_⟩
  have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn)
  rw [Nat.card_divisors hn]
  push_cast
  rw [hn', ← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  set f : ℕ → ℝ := fun p => if (p : ℝ) < (2 : ℝ) ^ (1 / ε) then M else 1
  have hf : ∏ p ∈ n.primeFactors, f p ≤ M ^ B := by
    have hM1 : 1 ≤ M := le_max_left _ _
    calc ∏ p ∈ n.primeFactors, f p = ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε)), M := by
            rw [Finset.prod_filter]
      _ = M ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε))).card := Finset.prod_const _
      _ ≤ M ^ B := by
            apply pow_le_pow_right₀ hM1
            calc _ ≤ (Finset.range B).card := by
                  apply Finset.card_le_card
                  intro p hp
                  simp only [Finset.mem_filter] at hp
                  simp only [Finset.mem_range]
                  have := lt_of_lt_of_le hp.2 (Nat.le_ceil _)
                  exact_mod_cast this
              _ = B := Finset.card_range B
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (f p * ((p : ℝ) ^ n.factorization p) ^ ε) := by
        apply Finset.prod_le_prod (fun p _ => by positivity)
        intro p hp
        have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
        obtain ⟨hA, hB⟩ := succ_le_mul_pow_rpow_of_two_le ε hε p (n.factorization p) h2
        simp only [f]
        split_ifs with h
        · exact hA
        · rw [one_mul]; exact hB (not_lt.mp h)
    _ = (∏ p ∈ n.primeFactors, f p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        Finset.prod_mul_distrib
    _ ≤ M ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        mul_le_mul_of_nonneg_right hf (Finset.prod_nonneg (fun p _ => by positivity))

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem sum_integral_separated_windows_le (h : ℝ → ℝ) (hc : Continuous h) (hpos : ∀ t, 0 ≤ h t)
    (S : Finset ℝ) (r T : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * r ≤ |a - b|)
    (hin : ∀ a ∈ S, -T ≤ a - r ∧ a + r ≤ T) (hTT : -T ≤ T) :
    ∑ a ∈ S, ∫ t in (a - r)..(a + r), h t ≤ ∫ t in (-T)..T, h t := by
  rw [intervalIntegral.integral_of_le hTT]
  have hwin : ∀ a ∈ S, ∫ t in (a - r)..(a + r), h t = ∫ t in Set.Ioc (a - r) (a + r), h t :=
    fun a _ => intervalIntegral.integral_of_le (by linarith)
  rw [Finset.sum_congr rfl hwin]
  rw [← MeasureTheory.integral_biUnion_finset S (fun a _ => measurableSet_Ioc)]
  · apply MeasureTheory.setIntegral_mono_set
    · exact hc.integrableOn_Ioc
    · exact Filter.Eventually.of_forall (fun t => hpos t)
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht' : t ∈ ⋃ a ∈ S, Set.Ioc (a - r) (a + r) := ht
      rw [Set.mem_iUnion₂] at ht'
      obtain ⟨a, ha, hta⟩ := ht'
      show t ∈ Set.Ioc (-T) T
      exact ⟨by linarith [(hin a ha).1, hta.1], by linarith [(hin a ha).2, hta.2]⟩
  · intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro t hta htb
    have := hsep a ha b hb hab
    rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at this <;>
      linarith [hta.1, hta.2, htb.1, htb.2]
  · intro a _
    exact hc.integrableOn_Ioc

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem mul_rpow_sub_one_le_rpow_sub_rpow (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) (x : ℝ) (hx : 1 ≤ x) :
    θ * x ^ (θ - 1) ≤ x ^ θ - (x - 1) ^ θ := by
  have hx0 : 0 < x := by linarith
  have hb : (1 + (-(1 / x))) ^ θ ≤ 1 + θ * (-(1 / x)) :=
    rpow_one_add_le_one_add_mul_self (by rw [neg_le_neg_iff, div_le_one hx0]; exact hx) h0.le h1
  have hsplit : (x - 1) ^ θ = x ^ θ * (1 + (-(1 / x))) ^ θ := by
    rw [← Real.mul_rpow hx0.le (by rw [← sub_eq_add_neg, sub_nonneg, div_le_one hx0]; exact hx)]
    congr 1; field_simp; ring
  have hpow : x ^ (θ - 1) = x ^ θ / x := by rw [Real.rpow_sub hx0, Real.rpow_one]
  rw [hsplit, hpow]
  have hxθ : 0 ≤ x ^ θ := by positivity
  have := mul_le_mul_of_nonneg_left hb hxθ
  have e : x ^ θ * (1 + θ * -(1 / x)) = x ^ θ - θ * (x ^ θ / x) := by field_simp; ring
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem sum_range_succ_rpow_sub_one_le (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (θ - 1) ≤ (N : ℝ) ^ θ / θ := by
  rw [le_div_iff₀ h0, Finset.sum_mul]
  calc ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (θ - 1) * θ
      ≤ ∑ k ∈ Finset.range N, ((((k + 1 : ℕ) : ℝ)) ^ θ - ((k : ℕ) : ℝ) ^ θ) := by
        apply Finset.sum_le_sum
        intro k _
        have := mul_rpow_sub_one_le_rpow_sub_rpow θ h0 h1 ((k : ℝ) + 1) (by linarith [k.cast_nonneg (α := ℝ)])
        push_cast
        rw [add_sub_cancel_right] at this
        linarith
    _ = (N : ℝ) ^ θ := by
        rw [Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ θ) N]
        simp [Real.zero_rpow h0.ne']

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private theorem sum_weighted_moebius_coeff_sq_le (K : ℝ) (hK : 0 < K)
    (hdiv : ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400))
    (Q : ℕ) (hQ : 2 ≤ Q) (σ : ℝ) (hσ : 1 - 3 / 800 ≤ σ) :
    ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) *
      ‖(if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then
        ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) else 0)‖ ^ 2 ≤ 3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  have hθ : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) ≤ 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    have h := sum_range_succ_rpow_sub_one_le (1 / 80) (by norm_num) (by norm_num) (Q ^ 6)
    have hre : ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((n : ℝ)) ^ ((1 : ℝ) / 80 - 1) =
        ∑ k ∈ Finset.range (Q ^ 6), ((k : ℝ) + 1) ^ ((1 : ℝ) / 80 - 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k _
      push_cast; ring_nf
    rw [hre]
    refine h.trans ?_
    have hQ0 : (0 : ℝ) ≤ Q := by positivity
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
    rw [div_eq_mul_inv, mul_comm]
    have : ((Q ^ 6 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) = (Q : ℝ) ^ ((6 : ℝ) / 80) := by
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0]; norm_num
    rw [this]
    norm_num
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ 3 * K ^ 2)).trans_eq (by ring))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  split_ifs with hI
  · have hnQ : Q ^ 3 < n := (Finset.mem_Ioc.mp hI).1
    have hweight : (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n ≤ 3 * n := by
      have : ((Q ^ 3 : ℕ) : ℝ) < n := by exact_mod_cast hnQ
      push_cast at this
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
      nlinarith [pow_le_pow_right₀ hQ1 (show 2 ≤ 3 by norm_num)]
    have hcoef : ‖((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ)‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400) := by
      refine le_trans ?_ (hdiv n (by omega))
      have hz : |∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ)| ≤
          (n.divisors.filter (fun d => d ≤ Q ^ 3)).card := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ 1 (fun d _ => ArithmeticFunction.abs_moebius_le_one)).trans ?_
        simp
      have hz' := hz.trans (by exact_mod_cast Finset.card_filter_le _ _ : ((n.divisors.filter (fun d => d ≤ Q ^ 3)).card : ℤ) ≤ n.divisors.card)
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast hz'
    have hpow : ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, hpow, mul_pow]
    calc ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) * (‖((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ)‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2)
        ≤ (3 * n) * ((K * (n : ℝ) ^ ((1 : ℝ) / 400)) ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by
          gcongr
      _ = 3 * K ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 200 + 1 - 2 * σ)) := by
          rw [show (1 : ℝ) / 200 + 1 - 2 * σ = (1 / 400) * 2 + 1 + (-σ) * 2 by ring,
            Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one, Real.rpow_mul hn0.le,
            Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]
          ring
      _ ≤ 3 * K ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 80 - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
  · simp only [norm_zero]
    norm_num
    positivity

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in

theorem _root_.GlobalTheory.SpacedDetected.card_spaced_detected_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, p.1 + 1 ≤ Q ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧ |p.2.2.im| ≤ Q ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖) → (∀ (N : ℕ) (χ : DirichletCharacter ℂ (N + 1)) (ρ ρ' : ℂ), (⟨N, χ, ρ⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → (⟨N, χ, ρ'⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → ρ ≠ ρ' → 1 ≤ |ρ.im - ρ'.im|) → (T.card : ℝ) ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨C₁, hC₁, hmv⟩ := _root_.GlobalTheory.norm_sq_le_integral_square
  obtain ⟨C₂, hC₂, hls⟩ := _root_.GlobalTheory.HybridLargeSieve.hybrid_large_sieve
  obtain ⟨K, hK, hdiv⟩ := exists_card_divisors_le_mul_rpow (1 / 400) (by norm_num)
  refine ⟨4 * (C₁ / (1 / 800) ^ 2) * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80))), by positivity, ?_⟩
  intro Q hQ T hT hsep
  set r : ℝ := 1 / 800 with hr
  set c : ℕ → ℂ := fun n => ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ)
    with hc
  set F : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℂ → ℂ :=
    fun x s => _root_.GlobalTheory.SpacedDetected.poly Q c x s with hF
  have hFdiff : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [hF, _root_.GlobalTheory.SpacedDetected.poly]
    intro s
    apply DifferentiableAt.fun_sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _
  set Tm : ℝ := Q + 1 with hTm
  set σ₀ : ℝ := 1 - 1 / 400 - r with hσ₀
  set σ₁ : ℝ := 1 + r with hσ₁
  set G : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ → ℝ :=
    fun x σ => ∫ t in (-Tm)..Tm, ‖F x (σ + t * I)‖ ^ 2 with hG
  have hGcont : ∀ x, Continuous (G x) := by
    intro x
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have := (hFdiff x).continuous
    fun_prop
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hpt : ∀ p ∈ T, (1 / 4 : ℝ) ≤ C₁ / r ^ 2 * ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 := by
    intro p hp
    obtain ⟨-, -, hre1, hre2, -, hbig⟩ := hT p hp
    have hval : F ⟨p.1, p.2.1⟩ p.2.2 = ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2) := rfl
    have h14 : (1 / 4 : ℝ) ≤ ‖F ⟨p.1, p.2.1⟩ p.2.2‖ ^ 2 := by
      rw [hval]; nlinarith
    refine h14.trans ((hmv _ p.2.2 r (hFdiff _) (by rw [hr]; norm_num)).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcont : Continuous (fun σ : ℝ => ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      have := (hFdiff ⟨p.1, p.2.1⟩).continuous
      fun_prop
    apply intervalIntegral.integral_mono_interval
    · rw [hσ₀]; linarith
    · rw [hr]; linarith
    · rw [hσ₁]; linarith
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      exact intervalIntegral.integral_nonneg (by rw [hr]; linarith) (fun t _ => by positivity)
    · exact hcont.intervalIntegrable _ _
  set P := T.image (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))) with hP
  have hgroup : ∑ p ∈ T, ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 ≤
      ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ := by
    have hW : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (a : ℝ), Continuous (fun σ : ℝ =>
        ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2) := by
      intro x a
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      have := (hFdiff x).continuous
      fun_prop
    have hle : σ₀ ≤ σ₁ := by rw [hσ₀, hσ₁, hr]; norm_num
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := P)
      (g := fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)))
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_le_sum
    intro x _
    rw [← intervalIntegral.integral_finset_sum (fun p _ => (hW _ _).intervalIntegrable _ _)]
    apply intervalIntegral.integral_mono_on hle
    · exact (continuous_finset_sum _ (fun p _ => hW _ _)).intervalIntegrable _ _
    · exact (hGcont x).intervalIntegrable _ _
    intro σ _
    set fib := T.filter (fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = x) with hfib
    have hrw : ∀ p ∈ fib, (∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) =
        ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F x (σ + t * I)‖ ^ 2 := by
      intro p hp
      rw [hfib, Finset.mem_filter] at hp
      rw [hp.2]
    rw [Finset.sum_congr rfl hrw]
    have hinj : Set.InjOn (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2.im) fib := by
      intro p hp p' hp' him
      rw [Finset.mem_coe, hfib, Finset.mem_filter] at hp hp'
      obtain ⟨N, χ, ρ⟩ := p
      obtain ⟨N', χ', ρ'⟩ := p'
      have hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩ := hp.2.trans hp'.2.symm
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hkey
      cases h
      by_contra hne
      have hρ : ρ ≠ ρ' := fun e => hne (by rw [e])
      have := hsep N χ ρ ρ' hp.1 hp'.1 hρ
      simp only at him
      rw [him, sub_self, abs_zero] at this
      norm_num at this
    rw [← Finset.sum_image (f := fun a => ∫ t in (a - r)..(a + r), ‖F x (σ + t * I)‖ ^ 2) hinj]
    apply sum_integral_separated_windows_le (fun t => ‖F x (σ + t * I)‖ ^ 2)
      (by have := (hFdiff x).continuous; fun_prop) (fun t => by positivity) _ r Tm (by rw [hr]; norm_num)
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨p', hp', rfl⟩ := hb
      rw [hfib, Finset.mem_filter] at hp hp'
      obtain ⟨N, χ, ρ⟩ := p
      obtain ⟨N', χ', ρ'⟩ := p'
      have hkey : (⟨N, χ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) = ⟨N', χ'⟩ := hp.2.trans hp'.2.symm
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hkey
      cases h
      have hρ : ρ ≠ ρ' := fun e => hab (by rw [e])
      have := hsep N χ ρ ρ' hp.1 hp'.1 hρ
      simp only
      rw [hr]; linarith
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      rw [hfib, Finset.mem_filter] at hp
      have hb := (hT p hp.1).2.2.2.2.1
      rw [abs_le] at hb
      rw [hTm, hr]
      constructor <;> linarith [hb.1, hb.2]
    · rw [hTm]; linarith
  have hsieve : ∀ σ ∈ Set.Icc σ₀ σ₁, ∑ x ∈ P, G x σ ≤ C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    intro σ hσ
    set a : ℕ → ℂ := fun n => if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) else 0
      with ha
    have hsub : Finset.Ioc (Q ^ 3) (Q ^ 6) ⊆ Finset.Icc 1 (Q ^ 6) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨by have := Nat.zero_le (Q ^ 3); omega, hn.2⟩
    have hrepr : ∀ (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (t : ℝ),
        F x (σ + t * I) = ∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I)) := by
      intro x t
      rw [← Finset.sum_subset hsub (fun n _ hn => by rw [ha]; simp [hn])]
      simp only [hF, _root_.GlobalTheory.SpacedDetected.poly, hc]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast (show n ≠ 0 by omega)
      rw [ha]
      simp only [if_pos hn]
      rw [neg_add, Complex.cpow_add _ _ hn0]
      ring
    set H : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ := fun x =>
      ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2
      with hH
    have hGH : ∀ x, G x σ = H x := by
      intro x
      simp only [hG, hH, hrepr]
    have hTm1 : (1 : ℝ) ≤ Tm := by rw [hTm]; linarith
    have hHnn : ∀ x, 0 ≤ H x := fun x =>
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    simp only [hGH]
    have hPsub : P ⊆ (Finset.range Q).sigma (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive)) := by
      intro x hx
      rw [hP, Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨h1, h2, -⟩ := hT p hp
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      exact ⟨by show p.1 < Q; omega, Finset.mem_univ _, h2⟩
    calc ∑ x ∈ P, H x ≤ ∑ x ∈ (Finset.range Q).sigma (fun q => Finset.univ.filter (fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive)), H x :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun x _ _ => hHnn x)
      _ = ∑ q ∈ Finset.range Q, ∑ᶠ (χ : DirichletCharacter ℂ (q + 1)) (_ : χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}),
            ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * χ n * (n : ℂ) ^ (-(t * I))‖ ^ 2 := by
          rw [Finset.sum_sigma]
          apply Finset.sum_congr rfl
          intro q _
          rw [finsum_mem_eq_toFinset_sum, Set.toFinset_setOf]
      _ ≤ C₂ * ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * Tm + n) * ‖a n‖ ^ 2 :=
          hls Q (Q ^ 6) a Tm (by omega) hTm1
      _ ≤ C₂ * (3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          have hσ' : 1 - 3 / 800 ≤ σ := by
            have := hσ.1; rw [hσ₀, hr] at this; linarith
          exact sum_weighted_moebius_coeff_sq_le K hK hdiv Q hQ σ hσ'
      _ = C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by ring
  have hint : ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ ≤ (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
    rw [← intervalIntegral.integral_finset_sum (fun x _ => (hGcont x).intervalIntegrable _ _)]
    have hle : σ₀ ≤ σ₁ := by rw [hσ₀, hσ₁, hr]; norm_num
    calc ∫ σ in σ₀..σ₁, ∑ x ∈ P, G x σ ≤ ∫ σ in σ₀..σ₁, C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
          apply intervalIntegral.integral_mono_on hle
          · exact (continuous_finset_sum _ (fun x _ => hGcont x)).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · exact hsieve
      _ = (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hσ₀, hσ₁, hr]; norm_num
  have hsum : (T.card : ℝ) * (1 / 4) ≤ C₁ / r ^ 2 * ∑ p ∈ T, ∫ σ in σ₀..σ₁,
      ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc (T.card : ℝ) * (1 / 4) = ∑ p ∈ T, (1 / 4 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hCr : 0 ≤ C₁ / r ^ 2 := by positivity
  calc (T.card : ℝ) = 4 * ((T.card : ℝ) * (1 / 4)) := by ring
    _ ≤ 4 * (C₁ / r ^ 2 * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hsum.trans (mul_le_mul_of_nonneg_left (hgroup.trans hint) hCr)
    _ = _ := by rw [hr]; ring

end GlobalTheory.SpacedDetected
