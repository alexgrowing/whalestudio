import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sqN_eq (N n : ℕ) : sqN N n = if IsSquare n ∧ n.Coprime N then 1 else 0 := by
  unfold sqN
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨m, rfl, hm⟩
    exact ⟨⟨m, rfl⟩, Nat.Coprime.mul_left hm hm⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    exact ⟨m, rfl, Nat.Coprime.coprime_mul_right hm⟩

private theorem isSquare_left {m n : ℕ} (h : m.Coprime n) (hs : IsSquare (m * n)) : IsSquare m := by
  obtain ⟨c, hc⟩ := hs
  have hu : IsUnit (gcd m n) := by
    rw [gcd_eq_nat_gcd, h.gcd_eq_one]; exact isUnit_one
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (c := c) (k := 2) hu (by rw [hc, sq])
  exact ⟨d, by rw [hd, sq]⟩

private theorem sqN_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) :
    sqN N (m * n) = sqN N m * sqN N n := by
  have e : (IsSquare (m * n) ∧ (m * n).Coprime N) ↔
      ((IsSquare m ∧ m.Coprime N) ∧ (IsSquare n ∧ n.Coprime N)) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨isSquare_left h h1, Nat.Coprime.coprime_mul_right h2⟩,
        ⟨isSquare_left h.symm (by rwa [mul_comm]), Nat.Coprime.coprime_mul_left h2⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1.mul h3, Nat.Coprime.mul_left h2 h4⟩
  rw [sqN_eq, sqN_eq, sqN_eq]
  by_cases h1 : IsSquare m ∧ m.Coprime N
  · by_cases h2 : IsSquare n ∧ n.Coprime N
    · rw [if_pos h1, if_pos h2, if_pos (e.2 ⟨h1, h2⟩), mul_one]
    · rw [if_neg h2, if_neg (fun x => h2 (e.1 x).2), mul_zero]
  · rw [if_neg h1, if_neg (fun x => h1 (e.1 x).1), zero_mul]

private theorem sqN_one (N : ℕ) : sqN N 1 = 1 := by
  rw [sqN_eq, if_pos ⟨⟨1, rfl⟩, Nat.coprime_one_left N⟩]

private theorem isSquare_pow_iff {p : ℕ} (hp : p.Prime) (j : ℕ) : IsSquare (p ^ j) ↔ Even j := by
  constructor
  · rintro ⟨m, hm⟩
    have hd : m ∣ p ^ j := ⟨m, hm⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [← pow_add] at hm
    exact ⟨i, Nat.pow_right_injective hp.two_le hm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ i, pow_add p i i⟩

private theorem conv_pow (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution f g (p ^ k) =
      PowerSeries.coeff k ((PowerSeries.mk fun i => f (p ^ i)) * PowerSeries.mk fun i => g (p ^ i)) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p ^ i) * g (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hp.pos]

private theorem sq_series (N : ℕ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N) :
    (1 - PowerSeries.X ^ 2) * (PowerSeries.mk fun i => sqN N (p ^ i)) = (1 : PowerSeries ℂ) := by
  have hc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hs : ∀ j, sqN N (p ^ j) = if Even j then 1 else 0 := by
    intro j
    rw [sqN_eq]
    refine if_congr ?_ rfl rfl
    rw [isSquare_pow_iff hp]
    exact ⟨fun x => x.1, fun x => ⟨x, Nat.Coprime.pow_left j hc⟩⟩
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_mk, hs]
  rcases k with _ | _ | k
  · simp
  · simp
  · have e : Even (k + 1 + 1) ↔ Even k := by
      rw [Nat.even_add_one, Nat.even_add_one, not_not]
    have e2 : k + 1 + 1 - 2 = k := by omega
    rw [if_pos (show 2 ≤ k + 1 + 1 by omega), e2, if_neg (show ¬ (k + 1 + 1 = 0) by omega)]
    simp only [e, sub_self]

private theorem isMul_of (f : ℕ → ℂ) (h1 : f 1 = 1)
    (h : ∀ m n, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n) :
    (toArithmeticFunction f).IsMultiplicative := by
  have key : ∀ n, toArithmeticFunction f n = if n = 0 then 0 else f n := fun _ => rfl
  refine ⟨by rw [key, if_neg one_ne_zero, h1], ?_⟩
  intro m n hmn
  rw [key, key, key]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    h m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn]

theorem UpperTheory.eq_convolution_squareIndicator_of_euler_factors :
    ∀ (N : ℕ) (a b : ℕ → ℂ), 0 < N → a 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
          (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) → b 1 = 1 →
          (∀ m n, 0 < m → 0 < n → m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime N → b n = 0) →
          (∀ p : ℕ, p.Prime → ¬ p ∣ N → (PowerSeries.mk fun k => a (p ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => b (p ^ k)) →
          ∀ n, n ≠ 0 → a n = LSeries.convolution b (sqN N) n := by
  intro N a b _ ha1 ham hap hb1 hbm hb0 hps n hn
  have hA := isMul_of a ha1 (fun m n _ _ h => ham m n h)
  have hB := isMul_of b hb1 hbm
  have hS := isMul_of (sqN N) (sqN_one N) (fun m n _ _ h => sqN_mul N h)
  have hE : toArithmeticFunction a = toArithmeticFunction b * toArithmeticFunction (sqN N) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ (hB.mul hS)]
    intro p i hp
    have e1 : toArithmeticFunction a (p ^ i) = a (p ^ i) := if_neg (pow_ne_zero i hp.ne_zero)
    rw [e1]
    change a (p ^ i) = LSeries.convolution b (sqN N) (p ^ i)
    rw [conv_pow _ _ hp]
    by_cases hd : p ∣ N
    · have hnc : ∀ j, ¬ (p ^ (j + 1)).Coprime N := fun j hc =>
        (Nat.Prime.coprime_iff_not_dvd hp).1
          (Nat.Coprime.coprime_dvd_left (dvd_pow_self p (Nat.succ_ne_zero j)) hc) hd
      have eb : (PowerSeries.mk fun i => b (p ^ i)) = 1 := by
        ext j
        rcases j with _ | j
        · simp [hb1]
        · rw [PowerSeries.coeff_mk, hb0 _ (hnc j), PowerSeries.coeff_one,
            if_neg (Nat.succ_ne_zero j)]
      rw [eb, one_mul, PowerSeries.coeff_mk]
      rcases i with _ | i
      · rw [pow_zero, ha1, sqN_one]
      · rw [hap p i hp hd, sqN_eq, if_neg (fun x => hnc i x.2)]
    · rw [← hps p hp hd, mul_assoc, sq_series N hp hd, mul_one, PowerSeries.coeff_mk]
  have e1 : toArithmeticFunction a n = a n := if_neg hn
  rw [← e1, hE]
  rfl
