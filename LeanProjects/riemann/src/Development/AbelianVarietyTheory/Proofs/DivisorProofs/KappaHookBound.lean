import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaFormulaHookSchurStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookQuotientCoefficientBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeHomogeneousBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeDerivativeRatioBoundStatement

open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.KapBound

theorem iterate_pderiv_mul {σ : Type} (i : σ) (n : ℕ) (P Q : MvPolynomial σ ℝ) :
    (pderiv i)^[n] (P * Q) = ∑ ij ∈ antidiagonal n,
      (n.choose ij.1 : MvPolynomial σ ℝ) * ((pderiv i)^[ij.1] P * (pderiv i)^[ij.2] Q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_mul
      (fun a b => (pderiv i)^[a] P * (pderiv i)^[b] Q) n, Function.iterate_succ_apply', ih, map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have h : n.choose ij.2 = n.choose ij.1 := by
      rw [← mem_antidiagonal.mp hij, Nat.choose_symm_add]
    rw [h, Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
    ring

theorem pderiv_shift {σ : Type} (i : σ) (a : ℝ) (P : MvPolynomial σ ℝ) :
    pderiv i (aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) P) =
      aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, aeval_X, pderiv_C, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [pderiv_X_of_ne h]

theorem iterate_pderiv_shift {σ : Type} (i : σ) (a : ℝ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    (pderiv i)^[n] (aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) P) =
      aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) ((pderiv i)^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pderiv_shift, Function.iterate_succ_apply']

theorem eval_shift {σ : Type} (a : ℝ) (v : σ → ℝ) (P : MvPolynomial σ ℝ) :
    eval (fun j => v j - a) (aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) P) = eval v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, aeval_X, map_add, eval_X, eval_C, sub_add_cancel]

theorem eval_iterate_of_shift {σ : Type} (i : σ) (a : ℝ) (n : ℕ) (v : σ → ℝ) (P : MvPolynomial σ ℝ)
    (h : aeval (fun j : σ => (X j + C a : MvPolynomial σ ℝ)) P = P) :
    eval v ((pderiv i)^[n] P) = eval (fun j => v j - a) ((pderiv i)^[n] P) := by
  rw [← eval_shift a v, ← iterate_pderiv_shift, h]

theorem abs_kap_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ) (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) (g U : ℝ) (τ τ' : ι) (i : Fin N) (k : ℕ), 0 < g → (∀ τ a b, a ≠ b → u τ a ≠ u τ b) → IsDecomp u Q → 2 ≤ k → k ≤ N → (∀ a b, u τ a - u τ b ≤ U) → (∀ a, a ≠ i → g ≤ |u τ' i - u τ' a|) → |kap u k (X (τ', i) ^ (k - 1)) (Q τ k)| ≤ 2 ^ (k - 1) / (k.factorial : ℝ) * U * ((N : ℝ) * (1 + U / g)) ^ (k - 1) := by
  intro ι _ _ N u Q g U τ τ' i k hg hreg hQ hk hkN hU hsep
  have hU0 : 0 ≤ U := by simpa using hU i i
  obtain ⟨rr, hhom, hR, hmass⟩ := GlobalTheory.T.hook_quotient_coefficient_bound N k (by omega) hkN
  obtain ⟨hsR, hsE⟩ := GlobalTheory.T.hook_translation_invariant N k (u τ i) hk hkN
  set m : ℝ := 2 ^ (k - 1) / (k.factorial : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  set w : Fin N → ℝ := fun j => u τ j - u τ i with hw
  have hwU : ∀ a, |w a| ≤ U := fun a => abs_sub_le_iff.mpr ⟨hU a i, hU i a⟩
  have hder : ∀ n, n ≤ k → |eval w ((pderiv i)^[n] rr)| ≤ m * (k : ℝ) ^ n * U ^ (k - n) := by
    intro n hn
    refine (GlobalTheory.T.iterated_derivative_homogeneous_bound N k n rr i U w hhom hn hU0 hwU).trans ?_
    gcongr
  have hE0 : eval (u τ) (detE (rho N)) = eval w (detE (rho N)) :=
    eval_iterate_of_shift i (u τ i) 0 (u τ) _ hsE
  have hRn : ∀ n, eval (u τ) ((pderiv i)^[n] (hookR N k)) = eval w ((pderiv i)^[n] (hookR N k)) :=
    fun n => eval_iterate_of_shift i (u τ i) n (u τ) _ hsR
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  rw [GlobalTheory.T.kappa_formula_hook_schur ι N u Q hreg hQ τ τ' i (l + 1) (by omega) hkN]
  simp only [Nat.add_sub_cancel] at *
  split_ifs with h
  · subst h
    have hs : ∀ n, |eval w ((pderiv i)^[n] (detE (rho N))) / eval w (detE (rho N))| ≤
        ((N : ℝ) / g) ^ n := by
      intro n
      refine GlobalTheory.T.vandermonde_derivative_ratio_bound N n w i g hg ?_ ?_
      · intro a b hab h
        exact hreg τ' a b hab (by simpa [hw] using h)
      · intro a ha
        have : w i - w a = u τ' i - u τ' a := by simp only [hw]; ring
        rw [this]; exact hsep a ha
    rw [abs_neg, hE0, hRn, hR, iterate_pderiv_mul, map_sum, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have e : (N : ℝ) * (1 + U / g) = N + U * (N / g) := by ring
    rw [e, Commute.add_pow' (Commute.all _ _), Finset.mul_sum]
    refine Finset.sum_le_sum fun ij hij => ?_
    have hl := mem_antidiagonal.mp hij
    have h1 := hder ij.1 (by omega)
    have h2 := hs ij.2
    have e2 : l + 1 - ij.1 = ij.2 + 1 := by omega
    rw [e2] at h1
    rw [map_mul, map_mul, map_natCast, mul_div_assoc, mul_div_assoc, abs_mul, abs_mul, Nat.abs_cast,
      nsmul_eq_mul]
    calc _ ≤ (l.choose ij.1 : ℝ) * ((m * (N : ℝ) ^ ij.1 * U ^ (ij.2 + 1)) * ((N : ℝ) / g) ^ ij.2) := by
          gcongr
          refine h1.trans ?_
          gcongr
      _ = _ := by ring
  · have h1 := hder 0 (by omega)
    have h2 := GlobalTheory.T.vandermonde_derivative_ratio_bound N l (u τ') i g hg (hreg τ') hsep
    have h3 : |eval (u τ) (hookR N (l + 1)) / eval (u τ) (detE (rho N))| ≤ m * U ^ (l + 1) := by
      have h4 := hRn 0
      simp only [Function.iterate_zero, id, pow_zero, mul_one, Nat.sub_zero] at h4 h1
      rw [h4, hE0, hR, map_mul, mul_div_assoc, abs_mul]
      have h5 : |eval w (detE (rho N)) / eval w (detE (rho N))| ≤ 1 := by
        rw [abs_div]; exact div_self_le_one _
      calc _ ≤ (m * U ^ (l + 1)) * 1 := by gcongr
        _ = _ := mul_one _
    rw [abs_neg, abs_mul]
    calc _ ≤ (m * U ^ (l + 1)) * ((N : ℝ) / g) ^ l := by gcongr
      _ = m * U * ((N : ℝ) * (U / g)) ^ l := by ring
      _ ≤ _ := by
        gcongr
        linarith

end GlobalTheory.KapBound
