import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqJac
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPairs
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagB
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwist
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainB
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum this

theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

theorem meanSquareHypW_of_pnt (hP : PNTAPRelW) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, MeanSquareHypW ε C x₀ := by
  intro ε hε hε1
  obtain ⟨xa, hxa⟩ := count_a hP Formalism.ZeroFreeDirichlet.excBound ε hε
  obtain ⟨xt, hxt⟩ := twist_bound hP Formalism.ZeroFreeDirichlet.zFRDirichlet Formalism.ZeroFreeDirichlet.excBound ε hε
  obtain ⟨C1, x1, h1⟩ := sum_cN_le
  obtain ⟨C2, x2, h2⟩ := exists_primePowerSum_le
  obtain ⟨C3, x3, h3⟩ := RR_cN_le
  obtain ⟨C4, x4, h4⟩ := sum_sP_sq_le
  refine ⟨|C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2,
    max (max xa xt) (max (max x1 x2) (max (max x3 x4) (max 3 ((19200 / ε) ^ (12 / ε))))), ?_⟩
  intro x X m₀ a₀ κ hx h8 hsm hcop ha4 hX1 hX2 hX3 hκ _
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxxa, hxxt⟩, ⟨hx1, hx2⟩, ⟨hx3, hx4⟩, hx5, hx6⟩ := hx
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h | h
    · subst h
      rw [Nat.coprime_zero_right] at hcop
      subst hcop
      norm_num at ha4
    · exact h
  refine ⟨hxa x X m₀ a₀ hxxa hm0 h8 hcop hX1 hX2 hX3, ?_⟩
  obtain ⟨ns0, hns0⟩ := hxt x X m₀ a₀ hxxt hm0 h8 hcop hX1 hX2 hX3
  set N := ⌊x ^ 400⌋₊ with hN
  set PP := PPset m₀ a₀ X with hPPdef

  obtain ⟨nstar, hns1, hns⟩ : ∃ nstar : ℕ, 1 < nstar ∧ ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ →
      s ≤ N ^ 2 → s ≠ nstar →
      |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * (PP.card : ℝ) := by
    by_cases hc : 1 < ns0
    · exact ⟨ns0, hc, hns0⟩
    · exact ⟨2, by norm_num, fun s hs1 hs2 hs3 hs4 hs5 _ => hns0 s hs1 hs2 hs3 hs4 hs5 (by omega)⟩
  have hc0 : ∀ n, 0 ≤ cN x n := cN_nonneg x hx0.le
  have hcpp : ∀ n, cN x n ≠ 0 → IsPrimePow n := cN_primePow x
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)

  have hbig : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q := by
    intro n hn n' hn' q hq
    rw [hPPdef, PPset, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hq2⟩, hqp, hqm, hqX⟩ := hq
    refine ⟨hqp, hqm, ?_⟩
    have hXpos : 0 < X := by
      by_contra hneg
      have : ⌊X⌋₊ = 0 := Nat.floor_of_nonpos (not_lt.mp hneg)
      omega
    have hpow := pow_le_sqrt_of_rpow_le_log ε hε x X hx5 hx6 hXpos hX2
    have hfl : ((N : ℕ) : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
    have hnr : (n : ℝ) ≤ x ^ 400 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hfl
    have hnr' : (n' : ℝ) ≤ x ^ 400 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn').2) hfl
    have hmul : (n : ℝ) * (n' : ℝ) ≤ x ^ 400 * x ^ 400 :=
      mul_le_mul hnr hnr' (Nat.cast_nonneg _) (by positivity)
    have h800 : x ^ 400 * x ^ 400 = x ^ 800 := by rw [← pow_add]
    have : ((n * n' : ℕ) : ℝ) < (q : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hPc : (0 : ℝ) ≤ (PP.card : ℝ) := Nat.cast_nonneg _
  have hη : (0 : ℝ) ≤ x ^ (-3 : ℝ) := Real.rpow_nonneg hx0.le _
  have step1 := meansq_expand PP (Icc 1 N) (cN x) hc0 κ hκ (fun n q => jacobiSym (n : ℤ) q)
  have step2 := meansq_split (Icc 1 N) (cN x) hc0 (fun n n' => soutPart m₀ (n * n'))
    (fun n n' => |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|) (PP.card : ℝ)
    (x ^ (-3 : ℝ)) hPc hη nstar
    (by
      intro n hn n' hn'
      show |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| ≤ _
      rw [abs_pair_sum_eq PP m₀ a₀ n n' h8 hcop (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn').1
        (hbig n hn n' hn')]
      exact abs_sum_jacobi_le PP _)
    (by
      intro n hn n' hn' e1 e2
      show |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| ≤ _
      have hn1 := (Finset.mem_Icc.mp hn)
      have hn1' := (Finset.mem_Icc.mp hn')
      rw [abs_pair_sum_eq PP m₀ a₀ n n' h8 hcop hn1.1 hn1'.1 (hbig n hn n' hn')]
      have hpos := soutPart_pos m₀ (n * n')
      refine hns _ (by change soutPart m₀ (n * n') ≠ 1 at e1; omega)
        (soutPart_odd m₀ _ (dvd_trans (by norm_num) h8)) (soutPart_squarefree m₀ _) (soutPart_coprime m₀ _) ?_ e2
      refine (soutPart_le m₀ _ (Nat.mul_pos hn1.1 hn1'.1)).trans ?_
      rw [sq]
      exact Nat.mul_le_mul hn1.2 hn1'.2)
  have hp1 := pairs_one (cN x) hc0 hcpp m₀ N
  have hB : ∀ p, sP (cN x) N p ≤ |C2| * Real.log x := fun p =>
    (h2 x hx2 p).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hl0)
  have hpr := pairs_r (cN x) hc0 hcpp m₀ N nstar hns1 (|C2| * Real.log x) hB
  have hy1 : (1 : ℝ) ≤ x ^ (ε / 5) := Real.one_le_rpow (by linarith) (by positivity)
  have hRR := h3 x hx3 m₀ (x ^ (ε / 5)) hy1 (by
    intro p hp hpm hpN
    rcases hsm p hp hpm with h | h
    · exact h
    · exfalso
      have hfl : ((N : ℕ) : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
      have : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
      linarith)
  have hfin := final_size ε hε1 x hx5 C1 C2 C3 C4 (∑ n ∈ Icc 1 N, cN x n)
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN x) N p ^ 2) (RR (cN x) m₀ N)
    (Finset.sum_nonneg fun n _ => hc0 n) (h1 x hx1) (h4 x hx4) (RR_nonneg _ hc0 _ _) hRR
  refine step1.trans (step2.trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ hPc
  linarith

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
