import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder

section Div

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def genAct (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ]
    MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  aeval fun v => if v.1 = τ then ∑ c : Fin n, C (X (v.2.1, c)) * X (τ, c, v.2.2) else X v

lemma map_genAct_X (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) (v : ι × Fin n × Fin n) :
    map (eval fun x => g x.1 x.2) (genAct τ (X v)) = famAct (Function.update (fun _ => 1) τ g) (X v) := by
  obtain ⟨τ', r, s⟩ := v
  by_cases hv : τ' = τ
  · subst hv
    simp only [genAct, famAct, aeval_X, if_true, Function.update_self, map_sum, map_mul, map_C, map_X,
      eval_X]
  · simp only [genAct, famAct, aeval_X, if_neg hv, Function.update_of_ne hv, map_X]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [Matrix.one_apply_ne (Ne.symm hc), map_zero, zero_mul])
      (by simp), Matrix.one_apply_eq, map_one, one_mul]

lemma map_genAct (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    map (eval fun x => g x.1 x.2) (genAct τ P) = famAct (Function.update (fun _ => 1) τ g) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [genAct, famAct]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_genAct_X]

def pushφ (φ : Module.Dual ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ)) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ m ∈ Q.support, φ (monomial m 1) • Q.coeff m

lemma eval_pushφ (φ : Module.Dual ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ)) (x : Fin n × Fin n → ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ)) :
    eval x (pushφ φ Q) = φ (map (eval x) Q) := by
  conv_rhs => rw [Q.as_sum]
  rw [pushφ, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, smul_eval]
  have : (monomial m (eval x (Q.coeff m)) : MvPolynomial (ι × Fin n × Fin n) ℂ) = eval x (Q.coeff m) • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

def elem (a b : Fin n) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + replicateCol (Fin 1) (Pi.single b t) * replicateRow (Fin 1) (Pi.single a (1 : ℂ))

lemma elem_apply (a b : Fin n) (t : ℂ) (r c : Fin n) :
    elem a b t r c = (if r = c then 1 else 0) + (if r = b ∧ c = a then t else 0) := by
  simp only [elem, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
  by_cases h1 : r = b <;> by_cases h2 : c = a <;> simp [h1, h2]

lemma famAct_elem_X (τ : ι) (a b : Fin n) (t : ℂ) (v : ι × Fin n × Fin n) :
    famAct (Function.update (fun _ => 1) τ (elem a b t)) (X v) = (bigGen τ a b (X v)).eval (C t) := by
  obtain ⟨τ', r, s⟩ := v
  by_cases hv : τ' = τ
  · subst hv
    simp only [famAct, aeval_X, Function.update_self, elem_apply, map_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [if_neg (Ne.symm hc), map_zero, zero_mul]) (by simp),
      if_pos rfl, map_one, one_mul]
    simp only [bigGen, aeval_X, true_and, Polynomial.eval_add, Polynomial.eval_C]
    by_cases hb : r = b
    · subst hb
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg (by tauto), map_zero, zero_mul]) (by simp),
        if_pos ⟨rfl, rfl⟩, if_pos rfl, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    · rw [Finset.sum_eq_zero (fun c _ => by rw [if_neg (by tauto), map_zero, zero_mul]), if_neg hb,
        Polynomial.eval_zero]
  · simp only [famAct, bigGen, aeval_X, Function.update_of_ne hv, hv, false_and, if_false, add_zero,
      Polynomial.eval_C]
    rw [Finset.sum_eq_single r (fun c _ hc => by rw [Matrix.one_apply_ne (Ne.symm hc), map_zero, zero_mul])
      (by simp), Matrix.one_apply_eq, map_one, one_mul]

lemma famAct_elem (τ : ι) (a b : Fin n) (t : ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    famAct (Function.update (fun _ => 1) τ (elem a b t)) P = (bigGen τ a b P).eval (C t) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [famAct, bigGen]
  | add p q hp hq => rw [map_add, hp, hq, map_add, Polynomial.eval_add]
  | mul_X p v hp => rw [map_mul, hp, map_mul, Polynomial.eval_mul, famAct_elem_X]

lemma isUnit_one_add_elem (a b : Fin n) (m : ℕ) : IsUnit (1 + elem a b (m : ℂ)).det := by
  have h : 1 + elem a b (m : ℂ) =
      (2 : ℂ) • (1 + replicateCol (Fin 1) (Pi.single b ((m : ℂ) / 2)) * replicateRow (Fin 1) (Pi.single a (1 : ℂ))) := by
    ext r c
    rw [Matrix.add_apply, elem_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
      Pi.single_apply, smul_eq_mul]
    split_ifs <;> (try subst_vars) <;> (try simp_all) <;> ring
  have hR := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (Pi.single b ((m : ℂ) / 2))
    (Pi.single a (1 : ℂ))
  rw [h, det_smul]
  erw [hR]
  rw [isUnit_iff_ne_zero]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  simp only [dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  intro h0
  have := congrArg Complex.re h0
  by_cases hab : a = b
  · subst hab
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · simp [hab] at this

theorem divisor_closed_holds : DivClosedOf := by
  intro hDens ι _ _ n G hGd M hM τ a b k P hP
  by_contra hnot
  obtain ⟨φ, hφP, hφM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ0 : ∀ Q ∈ M, φ Q = 0 := by
    intro Q hQ
    have : φ Q ∈ M.map φ := Submodule.mem_map_of_mem hQ
    rw [hφM] at this
    exact (Submodule.mem_bot ℂ).mp this
  set p := pushφ φ (genAct τ P) with hp
  have hval : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      eval (fun x => g x.1 x.2) p = φ (famAct (Function.update (fun _ => 1) τ g) P) := by
    intro g; rw [hp, eval_pushφ, map_genAct]

  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G τ * g = G τ → eval (fun x => g x.1 x.2) p = 0 := by
    intro g hg
    rw [hval]
    apply hφ0
    apply hM _ _ P hP
    intro σ
    by_cases hσ : σ = τ
    · subst hσ; simpa using hg
    · simp [hσ]
  have hall : ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit (1 + g).det → eval (fun x => g x.1 x.2) p = 0 := by
    rcases hGd τ with hpd | hpd
    · exact hDens n (G τ) hpd p hU
    · refine hDens n (-G τ) hpd p fun g hg => hU g ?_
      have := congrArg Neg.neg hg
      simpa [Matrix.mul_neg, Matrix.neg_mul] using this

  set q := bigGen τ a b P with hq
  set r : Polynomial ℂ := q.sum fun j c => Polynomial.monomial j (φ c) with hr
  have hr_eval : ∀ t : ℂ, r.eval t = φ (q.eval (C t)) := by
    intro t
    rw [hr, Polynomial.sum_def, Polynomial.eval_finset_sum, Polynomial.eval_eq_sum (p := q), Polynomial.sum_def,
      map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (q.coeff j), MvPolynomial.C_mul', map_smul, smul_eq_mul,
      mul_comm]
  have hr0 : r = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ)) Nat.cast_injective
    intro m
    show r.eval (m : ℂ) = 0
    rw [hr_eval, ← famAct_elem, ← hval]
    exact hall _ (isUnit_one_add_elem a b m)
  have hcoeff : r.coeff k = φ (bigDiv τ a b k P) := by
    rw [hr, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single k (fun j _ hj => if_neg hj) (fun hk => by
      rw [if_pos rfl, Polynomial.notMem_support_iff.mp hk, map_zero])]
    rw [if_pos rfl]
    rfl
  apply hφP
  rw [← hcoeff, hr0, Polynomial.coeff_zero]

end Div

end Formalism.L2.SG.Pf.ColDictValCPf
