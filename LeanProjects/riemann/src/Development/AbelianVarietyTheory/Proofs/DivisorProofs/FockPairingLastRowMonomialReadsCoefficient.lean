import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = coeff (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (spl K n x) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (coeff β (spl K n x)) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add, LinearMap.add_apply, coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
