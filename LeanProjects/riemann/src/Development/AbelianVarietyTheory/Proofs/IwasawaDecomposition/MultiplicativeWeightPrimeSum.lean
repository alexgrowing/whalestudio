import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymEqOfModEqFourMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InPartMulOutPartMulSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSqCardPrimeFactorsOutPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPrimesResidueGeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumVonMangoldtLeTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquarefreePrimeSumExceptionalStatement

open Finset ArithmeticFunction

namespace GlobalTheory.Mem.An

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem squarefree_prod_primeFactors_filter (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Squarefree (∏ p ∈ m.primeFactors.filter P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes hp' hq').2 hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime.squarefree

theorem inPart_dvd_modulus (m₀ m : ℕ) : inPart m₀ m ∣ m₀ := by
  unfold inPart
  refine Finset.prod_primes_dvd _ ?_ ?_
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.1

theorem outPart_coprime_modulus (m₀ m : ℕ) : Nat.Coprime (outPart m₀ m) m₀ := by
  unfold outPart
  refine Nat.Coprime.prod_left ?_
  intro p hp
  exact (Nat.Prime.coprime_iff_not_dvd
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2 (Finset.mem_filter.1 hp).2.1

theorem outPart_le_self (m₀ m : ℕ) (hm : 0 < m) : outPart m₀ m ≤ m := by
  refine Nat.le_of_dvd hm ?_
  have h := GlobalTheory.inPart_mul_outPart_mul_sq m₀ m hm
  exact ((Dvd.intro_left _ rfl).mul_right _).trans (dvd_of_eq h)

theorem abs_sum_jacobiSym_le_outPart (m₀ a₀ m : ℕ) (S : Finset ℕ) (h8 : 8 ∣ m₀) (hm : 0 < m)
    (hS : ∀ q ∈ S, q % 4 = 3 ∧ q ≡ a₀ [MOD m₀] ∧ Nat.Coprime m q) :
    |∑ q ∈ S, (jacobiSym (m : ℤ) q : ℝ)| ≤ |∑ q ∈ S, (jacobiSym (q : ℤ) (outPart m₀ m) : ℝ)| := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · simp
  have hodd : ∀ q ∈ S, Odd q := fun q hq => by
    have := (hS q hq).1
    rw [Nat.odd_iff]; omega
  have hs : Odd (outPart m₀ m) := by
    have h2 : Nat.Coprime (outPart m₀ m) 2 :=
      (outPart_coprime_modulus m₀ m).coprime_dvd_right (Dvd.dvd.trans (by norm_num) h8)
    exact Nat.coprime_two_right.1 h2
  have key : ∀ q ∈ S, jacobiSym (m : ℤ) q =
      (jacobiSym (inPart m₀ m : ℤ) q₀ * (-1) ^ (outPart m₀ m / 2)) * jacobiSym (q : ℤ) (outPart m₀ m) := by
    intro q hq
    obtain ⟨h4, hc, hcop⟩ := hS q hq
    rw [GlobalTheory.jacobiInOut m₀ m q hm hcop,
      GlobalTheory.jacobiSym_const_on_class m₀ (inPart m₀ m) q q₀ h8 (inPart_dvd_modulus m₀ m)
        (squarefree_prod_primeFactors_filter _ _) (hodd q hq) (hodd q₀ hq₀) (hc.trans (hS q₀ hq₀).2.1.symm),
      jacobiSym.quadratic_reciprocity hs (hodd q hq), mul_comm (outPart m₀ m / 2), pow_mul,
      Odd.neg_one_pow (show Odd (q / 2) by rw [Nat.odd_iff]; omega), mul_assoc]
  rw [Finset.sum_congr rfl (fun q hq => by rw [key q hq, Int.cast_mul]), ← Finset.mul_sum, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  push_cast
  rw [abs_mul, abs_neg_one_pow, mul_one]
  rcases jacobiSym.trichotomy (inPart m₀ m : ℤ) q₀ with h | h | h <;> simp [h]

theorem rpow_lt_of_mem_PP {x X : ℝ} {m₀ a₀ q : ℕ} (hx : Real.exp 1600 ≤ x) (h8 : 8 ≤ m₀) (hX : 0 < X)
    (h1 : (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X) (hq : q ∈ PP m₀ a₀ X) :
    x ^ (400 : ℝ) < q := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 1600 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hm : 2 ≤ Real.log m₀ := by
    have h2 : Real.log 8 ≤ Real.log m₀ := Real.log_le_log (by norm_num) (by exact_mod_cast h8)
    have h3 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hq1 : Real.sqrt X < q := by
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hq).1).1
    exact (Nat.floor_lt (Real.sqrt_nonneg X)).1 this
  refine lt_of_le_of_lt ?_ hq1
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 _) (Real.sqrt_pos.2 hX), Real.log_rpow hx0,
    Real.log_sqrt hX.le]
  have h4 : Real.log x ^ 2 * 2 ≤ Real.log x ^ 2 * Real.log m₀ :=
    mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  nlinarith

theorem meanSq_primes_residue_le : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → a₀ % 4 = 3 → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ x ^ (400 : ℝ) < p) → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∀ κ : ℕ → ℂ, κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) → (∀ n, ‖κ n‖ ≤ 1) → (∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x κ p‖ ^ 2) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card ≤ C * x * Real.log x := by
  intro hTZ hPage hZ eps he he'
  obtain ⟨x₁, C', c', hC', hc', hmu⟩ := GlobalTheory.T.squarefree_prime_sum_exceptional hTZ hPage hZ eps he he'
  obtain ⟨x₂, hcard⟩ := card_primes_residue_ge_rpow hTZ eps he he'
  obtain ⟨x₃, C, hcore⟩ :=
    GlobalTheory.meanSq_core sum_vonMangoldt_le_two_mul eps he (by linarith) C' c' hC' hc'
  refine ⟨max (max x₁ x₂) (max x₃ (Real.exp 1600)), C, ?_⟩
  intro x hx m₀ a₀ h8 hm hcop ha hpr X hX h1 h2 κ hκ1 hκm hκb
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx4
  have h8' : 8 ≤ m₀ := Nat.le_of_dvd hm h8
  obtain ⟨nStar, hn⟩ := hmu x hx1 m₀ a₀ h8 hm hcop X hX h1 h2
  have hc := hcard x hx2 m₀ a₀ (by omega) hcop X hX h1 h2
  have hpos : (0 : ℝ) < (PP m₀ a₀ X).card := lt_of_lt_of_le (Real.rpow_pos_of_pos hX _) hc
  have hmem : ∀ q ∈ PP m₀ a₀ X, q.Prime ∧ q % 4 = 3 ∧ x ^ (400 : ℝ) < q := by
    intro q hq
    have h := (Finset.mem_filter.1 hq).2
    refine ⟨h.1, ?_, rpow_lt_of_mem_PP hx4 h8' hX h1 hq⟩
    have h4 : q ≡ a₀ [MOD 4] := h.2.of_dvd (Dvd.dvd.trans (by norm_num) h8)
    exact (show q % 4 = a₀ % 4 from h4).trans ha
  refine hcore x hx3 m₀ (PP m₀ a₀ X) κ nStar h8 hm hpr
    (Finset.card_pos.1 (by exact_mod_cast hpos)) hmem hκ1 hκm hκb ?_
  intro n n' hn1 hn2 _ _ hne1 hne2
  have hz : (0 : ℝ) ≤ x ^ (400 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  obtain ⟨hn1a, hn1b⟩ := Finset.mem_Icc.1 hn1
  obtain ⟨hn2a, hn2b⟩ := Finset.mem_Icc.1 hn2
  have hn1c : (n : ℝ) ≤ x ^ (400 : ℝ) := (Nat.le_floor_iff hz).1 hn1b
  have hn2c : (n' : ℝ) ≤ x ^ (400 : ℝ) := (Nat.le_floor_iff hz).1 hn2b
  have hnn : 0 < n * n' := Nat.mul_pos hn1a hn2a
  have hsq : Squarefree (outPart m₀ (n * n')) := squarefree_prod_primeFactors_filter _ _
  have hs1 : 1 < outPart m₀ (n * n') := by
    have := hsq.ne_zero
    omega
  have hsle : (outPart m₀ (n * n') : ℝ) ≤ x ^ (800 : ℝ) := by
    have h3 : (outPart m₀ (n * n') : ℝ) ≤ (n : ℝ) * n' := by exact_mod_cast outPart_le_self m₀ _ hnn
    have h4 : x ^ (800 : ℝ) = x ^ (400 : ℝ) * x ^ (400 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [h4]
    exact h3.trans (mul_le_mul hn1c hn2c (Nat.cast_nonneg _) hz)
  refine le_trans ?_ (hn _ hs1 hsq (outPart_coprime_modulus _ _) hsle hne2)
  rw [abs_div, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  refine abs_sum_jacobiSym_le_outPart m₀ a₀ (n * n') _ h8 hnn ?_
  intro q hq
  obtain ⟨hp, h4, hlt⟩ := hmem q hq
  refine ⟨h4, (Finset.mem_filter.1 hq).2.2, ?_⟩
  have hl : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ x ^ (400 : ℝ) → Nat.Coprime k q := fun k hk hk' =>
    (Nat.coprime_of_lt_prime (by omega) (by exact_mod_cast hk'.trans_lt hlt) hp).symm
  exact Nat.Coprime.mul_left (hl n hn1a hn1c) (hl n' hn2a hn2c)

end GlobalTheory.Mem.An
