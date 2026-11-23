import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private lemma conv_prime_pow (a a' : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution a a' (p ^ k) =
      PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k))) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => a x * a' y), Nat.divisors_prime_pow hp, Finset.sum_map,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a (p ^ i) * a' (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [Nat.pow_div hik hp.pos]

private lemma toAF_mult (a : ℕ → ℂ) (h1 : a 1 = 1)
    (hm : ∀ m n, m.Coprime n → a (m * n) = a m * a n) :
    (toArithmeticFunction a).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm0 hn0 hmn => ?_⟩
  · simp [toArithmeticFunction, h1]
  · simp [toArithmeticFunction, hm0, hn0, hm m n hmn]

private lemma conv_nonneg_of_pp (b : ArithmeticFunction ℂ) (hb : b.IsMultiplicative)
    (hpp : ∀ p k : ℕ, p.Prime → 0 ≤ b (p ^ k)) (n : ℕ) : 0 ≤ b n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [hb.multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp => hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))

theorem UpperTheory.false_of_landau_nonneg_euler_factors_entire :
    ∀ (a a' : ℕ → ℂ) (N : ℕ), 0 < N → a 1 = 1 → a' 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
        (∀ m n, m.Coprime n → a' (m * n) = a' m * a' n) → (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) →
        (∀ p k : ℕ, p.Prime → p ∣ N → a' (p ^ (k + 1)) = 0) →
        (∀ p : ℕ, p.Prime → ¬ p ∣ N →
          (∀ k, 0 ≤ PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) ∧
          1 ≤ PowerSeries.coeff 4 (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) →
        (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) → (∀ s : ℂ, 4 < s.re → LSeriesSummable a' s) → Entire a → Entire a' → Landau → False := by
  intro a a' N hN h1 h1' hm hm' hbad hbad' hgood hs hs' hE hE' hL
  have hmul : (toArithmeticFunction a * toArithmeticFunction a').IsMultiplicative :=
    (toAF_mult a h1 hm).mul (toAF_mult a' h1' hm')
  have hcoe : ∀ n, LSeries.convolution a a' n = (toArithmeticFunction a * toArithmeticFunction a') n :=
    fun n => rfl
  have hone : LSeries.convolution a a' 1 = 1 := by rw [hcoe, hmul.map_one]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ LSeries.convolution a a' (p ^ k) := by
    intro p k hp
    by_cases hpN : p ∣ N
    · rcases k with _ | k
      · simp [hone]
      · have hz : LSeries.convolution a a' (p ^ (k + 1)) = 0 := by
          rw [conv_prime_pow a a' hp, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun x hx => ?_
          obtain ⟨i, j⟩ := x
          have hij : i + j = k + 1 := by simpa using hx
          rcases i with _ | i
          · have hj : j = k + 1 := by omega
            subst hj
            simp [hbad' p k hp hpN]
          · simp [hbad p i hp hpN]
        exact hz.ge
    · rw [conv_prime_pow a a' hp]
      exact (hgood p hp hpN).1 k
  have hnn : ∀ n, 0 ≤ LSeries.convolution a a' n :=
    conv_nonneg_of_pp _ hmul hpp
  have hsum : ∀ s : ℂ, 4 < s.re → LSeriesSummable (LSeries.convolution a a') s :=
    fun s h => (hs s h).convolution (hs' s h)
  have hent : Entire (LSeries.convolution a a') := by
    obtain ⟨F, hF, hFe⟩ := hE
    obtain ⟨G, hG, hGe⟩ := hE'
    refine ⟨fun s => F s * G s, hF.mul hG, fun s h => ?_⟩
    rw [LSeries_convolution' (hs s h) (hs' s h)]
    show F s * G s = _
    rw [hFe s h, hGe s h]
  have hfin := hL _ hnn hone hsum hent
  have hfin' : ((fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n}).Finite :=
    hfin.preimage fun x _ y _ h => (Nat.pow_left_inj (by norm_num)).1 h
  obtain ⟨M, hM⟩ := hfin'.bddAbove
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (max M N + 1)
  have hpN : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd hN h
    have := le_max_right M N
    omega
  have hmem : p ∈ (fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n} := by
    show 1 ≤ LSeries.convolution a a' (p ^ 4)
    rw [conv_prime_pow a a' hp]
    exact (hgood p hp hpN).2
  have := hM hmem
  have := le_max_left M N
  omega
