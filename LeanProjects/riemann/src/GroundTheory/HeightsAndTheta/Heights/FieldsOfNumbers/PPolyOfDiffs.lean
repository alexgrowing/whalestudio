import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

namespace PolyOfDiffs

variable {K : Type}

theorem totalDegree_aeval_le (g : K → MvPolynomial K ℚ) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (P : MvPolynomial K ℚ) : (aeval g P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun α hα => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  unfold Finsupp.prod
  refine (totalDegree_finsetProd _ _).trans
    ((Finset.sum_le_sum fun j _ => ?_).trans (le_totalDegree hα))
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (α j) (hg j))

variable [DecidableEq K]

theorem exists_pow_antideriv (a : ℕ) : ∃ F : Polynomial ℚ, F.natDegree ≤ a + 1 ∧
    ∀ x : ℚ, F.eval x - F.eval (x - 1) = x ^ a := by
  refine ⟨Polynomial.C ((a + 1 : ℚ)⁻¹) *
    (Polynomial.bernoulli (a + 1)).comp (Polynomial.X + 1), ?_, fun x => ?_⟩
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine Polynomial.natDegree_comp_le.trans ?_
    have hX : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
      rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_add_C 1
    rw [hX, mul_one, Polynomial.bernoulli]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)
  · have h := Polynomial.bernoulli_eval_one_add (a + 1) x
    rw [Nat.add_sub_cancel] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, sub_add_cancel]
    rw [add_comm x 1, h]
    push_cast
    field_simp
    ring

theorem eval_aeval_X (y : K → ℚ) (k : K) (F : Polynomial ℚ) :
    eval y (Polynomial.aeval (X k) F) = F.eval (y k) := by
  induction F using Polynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, Polynomial.eval_add]
  | monomial n a _ => simp

theorem exists_antideriv (k : K) (q : MvPolynomial K ℚ) : ∃ P : MvPolynomial K ℚ,
    P.totalDegree ≤ q.totalDegree + 1 ∧
    ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x q := by
  have key : ∀ α ∈ q.support, ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ q.totalDegree + 1 ∧
      ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x (monomial α (q.coeff α)) := by
    intro α hα
    obtain ⟨F, hFd, hF⟩ := exists_pow_antideriv (α k)
    refine ⟨monomial (α.erase k) (q.coeff α) * Polynomial.aeval (X k) F, ?_, fun x => ?_⟩
    · have hsum : ((α.erase k).sum fun _ e => e) + α k ≤ q.totalDegree := by
        refine le_trans (le_of_eq ?_) (le_totalDegree hα)
        conv_rhs => rw [← Finsupp.single_add_erase k α]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl, add_comm]
      have h1 : (monomial (α.erase k) (q.coeff α)).totalDegree ≤
          (α.erase k).sum fun _ e => e := totalDegree_monomial_le _ _
      have h2 : (Polynomial.aeval (X k : MvPolynomial K ℚ) F).totalDegree ≤ α k + 1 := by
        rw [Polynomial.aeval_eq_sum_range]
        refine totalDegree_finsetSum_le fun i hi => ?_
        refine (totalDegree_smul_le _ _).trans ?_
        rw [totalDegree_X_pow]
        exact (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hFd
      refine (totalDegree_mul _ _).trans ?_
      omega
    · have hmono : monomial α (q.coeff α) = monomial (α.erase k) (q.coeff α) * X k ^ (α k) := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, add_comm, Finsupp.single_add_erase]
      have hsh : eval (x - Pi.single k 1) (monomial (α.erase k) (q.coeff α)) =
          eval x (monomial (α.erase k) (q.coeff α)) := by
        simp only [eval_monomial]
        congr 1
        refine Finsupp.prod_congr fun j hj => ?_
        have hjk : j ≠ k := by
          rw [Finsupp.support_erase] at hj
          exact (Finset.mem_erase.1 hj).1
        simp [Pi.single_apply, hjk]
      have hev : ∀ y : K → ℚ, eval y (Polynomial.aeval (X k) F) = F.eval (y k) :=
        fun y => eval_aeval_X y k F
      rw [hmono, map_mul, map_mul, hsh, hev, hev, map_mul, map_pow, eval_X, ← mul_sub]
      congr 1
      rw [← hF (x k)]
      simp
  choose! P hPd hPe using key
  refine ⟨∑ α ∈ q.support, P α, totalDegree_finsetSum_le hPd, fun x => ?_⟩
  conv_rhs => rw [q.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun α hα => hPe α hα x

noncomputable def freeze (s : Finset K) (N : K → ℚ) : K → MvPolynomial K ℚ :=
  fun j => if j ∈ s then X j else C (N j)

theorem totalDegree_freeze_le (s : Finset K) (N : K → ℚ) (j : K) :
    (freeze s N j).totalDegree ≤ 1 := by
  unfold freeze
  split_ifs
  · exact (totalDegree_X j).le
  · rw [totalDegree_C]; exact zero_le_one

theorem eval_aeval_freeze (s : Finset K) (N x : K → ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval (freeze s N) P) = eval (fun j => if j ∈ s then x j else N j) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, map_add]
  | mul_X p j hp =>
    simp only [map_mul, hp, aeval_X, eval_X, freeze]
    split_ifs <;> simp

def pathPt (N : K → ℤ) (s : Finset K) (m : K → ℤ) : K → ℤ :=
  fun j => if j ∈ s then m j else N j

theorem proof : PolyOfDiffs.Statement := by
  intro K _ _ h d hq
  choose q hqd hqe using hq
  have hP : ∀ k, ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ d ∧
      ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x (q k) := by
    intro k
    rcases hqd k with h0 | hlt
    · exact ⟨0, by simp, fun x => by simp [h0]⟩
    · obtain ⟨P, hPd, hPe⟩ := exists_antideriv k (q k)
      exact ⟨P, hPd.trans hlt, hPe⟩
  choose P hPd hPe using hP
  have hqe' : ∀ k, ∀ᶠ m in Filter.atTop,
      ((diffStep (Pi.single k 1) h m : ℤ) : ℚ) = eval (fun j => (m j : ℚ)) (q k) := hqe
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hqe')

  have hstep : ∀ k, ∀ y : K → ℤ, N ≤ y → (h y : ℚ) - eval (fun j => (y j : ℚ)) (P k) =
      (h (y - Pi.single k 1) : ℚ) - eval (fun j => ((y - Pi.single k 1 : K → ℤ) j : ℚ)) (P k) := by
    intro k y hy
    have e1 := hN y hy k
    have e2 := hPe k (fun j => (y j : ℚ))
    have e3 : (fun j => (y j : ℚ)) - Pi.single k 1 = fun j => ((y - Pi.single k 1 : K → ℤ) j : ℚ) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    rw [e3] at e2
    simp only [diffStep] at e1
    push_cast at e1
    linarith

  have hline : ∀ k, ∀ x : K → ℤ, N ≤ x → x k = N k → ∀ t : ℤ, N k ≤ t →
      (h (Function.update x k t) : ℚ) - eval (fun j => (Function.update x k t j : ℚ)) (P k) =
      (h x : ℚ) - eval (fun j => (x j : ℚ)) (P k) := by
    intro k x hx hxk t ht
    induction t, ht using Int.le_induction with
    | base => rw [← hxk, Function.update_eq_self]
    | succ t ht ih =>
      have hy : N ≤ Function.update x k (t + 1) := by
        intro j
        by_cases hj : j = k
        · subst hj; simp; omega
        · simp [hj]; exact hx j
      have hsh : Function.update x k (t + 1) - Pi.single k 1 = Function.update x k t := by
        funext j
        by_cases hj : j = k
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hstep k _ hy, hsh, ih]

  have key : ∀ s : Finset K, ∃ Q : MvPolynomial K ℚ, Q.totalDegree ≤ d ∧
      ∀ m : K → ℤ, N ≤ m → (h (pathPt N s m) : ℚ) = eval (fun j => (m j : ℚ)) Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C (h N : ℚ), by rw [totalDegree_C]; exact Nat.zero_le _, fun m _ => ?_⟩
      have e : pathPt N ∅ m = N := by funext j; simp [pathPt]
      rw [e, eval_C]
    | insert k s hk ih =>
      obtain ⟨Q, hQd, hQ⟩ := ih
      refine ⟨Q + aeval (freeze (insert k s) (fun j => (N j : ℚ))) (P k) -
        aeval (freeze s (fun j => (N j : ℚ))) (P k), ?_, fun m hm => ?_⟩
      · refine (totalDegree_sub _ _).trans
          (max_le ((totalDegree_add _ _).trans (max_le hQd ?_)) ?_)
        · exact (totalDegree_aeval_le _ (totalDegree_freeze_le _ _) _).trans (hPd k)
        · exact (totalDegree_aeval_le _ (totalDegree_freeze_le _ _) _).trans (hPd k)
      · have hx : N ≤ pathPt N s m := fun j => by
          simp only [pathPt]
          split_ifs
          · exact hm j
          · exact le_rfl
        have hxk : pathPt N s m k = N k := by simp [pathPt, hk]
        have hupd : pathPt N (insert k s) m = Function.update (pathPt N s m) k (m k) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [pathPt]
          · simp [pathPt, hj]
        have e := hline k (pathPt N s m) hx hxk (m k) (hm k)
        rw [← hupd] at e
        have c1 : ∀ t : Finset K, (fun j => ((pathPt N t m j : ℤ) : ℚ)) =
            fun j => if j ∈ t then (m j : ℚ) else (N j : ℚ) := by
          intro t; funext j; simp only [pathPt]; split_ifs <;> rfl
        rw [map_sub, map_add, eval_aeval_freeze, eval_aeval_freeze, ← hQ m hm, ← c1, ← c1]
        linarith
  obtain ⟨Q, hQd, hQ⟩ := key Finset.univ
  refine ⟨Q, hQd, ?_⟩
  rw [EventuallyPoly, Filter.eventually_atTop]
  refine ⟨N, fun m hm => ?_⟩
  have e : pathPt N Finset.univ m = m := by funext j; simp [pathPt]
  rw [← e]
  exact (hQ m hm).trans (by rw [e])

end PolyOfDiffs

end GroundTheory.Heights₂.Heights.FieldNumbers
