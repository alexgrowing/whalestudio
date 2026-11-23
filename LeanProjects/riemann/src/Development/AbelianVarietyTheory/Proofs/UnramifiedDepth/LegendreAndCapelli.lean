import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory.LegendreFacts

open GlobalTheory.LegendreBounds

theorem mfact_eq_prod {σ : Type} [Fintype σ] (A : σ →₀ ℕ) :
    mfact A = ∏ j, (A j).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)

theorem degree_eq_sum' {σ : Type} [Fintype σ] (A : σ →₀ ℕ) : A.degree = ∑ j, A j := by
  rw [Finsupp.degree_apply]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  simpa using hj

theorem capNat_mul (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by
  unfold capNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro c _
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))

private lemma padicValNat_factorial_eq_div_of_lt_sq (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : N < l ^ 2) :
    padicValNat l N.factorial = N / l := by
  have : Fact l.Prime := ⟨hl⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hpos.ne' hN)]
    simp

theorem legendre_facts : F2 := by
  intro l hl
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hden : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    have h := legendre_real l hl N
    simpa using h
  · intro N _
    have h := digitSum_le l N hl.one_lt
    rw [Real.natFloor_logb_natCast]
    have hc : (((Nat.digits l N).sum : ℕ) : ℝ) ≤ (((Nat.log l N + 1) * (l - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hl.one_lt.le, Nat.cast_add, Nat.cast_one] at hc
    rw [mul_comm]
    exact hc
  · intro σ _ A hA
    rw [mfact_eq_prod, degree_eq_sum']
    rw [degree_eq_sum'] at hA
    constructor
    · have h := ((legendre_bounds l hl).2.1) σ (fun j => A j) hA
      simpa using h
    · rw [padicValNat_prod_factorial l hl Finset.univ (fun j => A j)]
      have hterm : ∀ j ∈ (Finset.univ : Finset σ),
          (padicValNat l (A j).factorial : ℝ) ≤ (A j : ℝ) / ((l : ℝ) - 1) :=
        fun j _ => upper l hl (A j)
      calc ∑ j, (padicValNat l (A j).factorial : ℝ)
          ≤ ∑ j, (A j : ℝ) / ((l : ℝ) - 1) := Finset.sum_le_sum hterm
        _ = ((∑ j, A j : ℕ) : ℝ) / ((l : ℝ) - 1) := by
          rw [← Finset.sum_div]
          push_cast
          rfl
  · intro N hN
    exact padicValNat_factorial_eq_div_of_lt_sq l hl N hN

theorem capelli_bound : F3 := by
  intro l hl n0 n x hn hn0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have : Fact l.Prime := ⟨hl⟩
  constructor
  · have hP : (∏ c ∈ Finset.range n0, c.factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero c)
    have hC : capNat n0 x ≠ 0 := by
      intro h0
      have h := capNat_mul n0 x
      rw [h0, zero_mul] at h
      exact (Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero (x + c))) h.symm
    have hv : padicValNat l (capNat n0 x) + padicValNat l (∏ c ∈ Finset.range n0, c.factorial)
        = padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) := by
      rw [← padicValNat.mul hC hP, capNat_mul]
    have hvR : (padicValNat l (capNat n0 x) : ℝ)
        = (padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) : ℝ)
          - (padicValNat l (∏ c ∈ Finset.range n0, c.factorial) : ℝ) := by
      rw [← hv]
      push_cast
      ring
    have h := ((legendre_bounds l hl).2.2) n0 x
    rw [hvR]
    exact h
  · have hlogn : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 (by exact_mod_cast hn)
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · subst h0
      have : (0 : ℝ) ≤ (n : ℝ) * (Real.logb l n + 1) := by positivity
      simpa using this
    · have hpos' : (0 : ℝ) < n0 := by exact_mod_cast hpos
      have hlog0 : 0 ≤ Real.logb l n0 := Real.logb_nonneg hl1 (by exact_mod_cast hpos)
      have hle : Real.logb l n0 ≤ Real.logb l n := Real.logb_le_logb_of_le hl1 hpos' hnn
      have : (n0 : ℝ) * (Real.logb l n0 + 1) ≤ n * (Real.logb l n + 1) :=
        mul_le_mul hnn (by linarith) (by linarith) (by positivity)
      linarith

end GlobalTheory.LegendreFacts
