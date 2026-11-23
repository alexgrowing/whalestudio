import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem exists_poly_backDiff_pow (n : ℕ) :
    ∃ P : Polynomial ℚ, ∀ t : ℚ, P.eval t - P.eval (t - 1) = t ^ n := by
  refine ⟨(1 / ((n : ℚ) + 1)) • (Polynomial.bernoulli (n + 1)).comp (Polynomial.X + 1), fun t => ?_⟩
  have h1 := Polynomial.bernoulli_eval_one_add (n + 1) (t - 1 + 1)
  simp only [Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, smul_eq_mul]
  rw [show (1 : ℚ) + (t - 1 + 1) = t + 1 by ring, show t - 1 + 1 = t by ring] at h1
  rw [show t - 1 + 1 = t by ring, h1]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem exists_mvpoly_backDiff {K : Type} [DecidableEq K] (k : K) (q : MvPolynomial K ℚ) :
    ∃ R : MvPolynomial K ℚ, ∀ x : K → ℚ, eval x R - eval (x - Pi.single k 1) R = eval x q := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨P, hP⟩ := exists_poly_backDiff_pow (u k)
    refine ⟨monomial (u.erase k) a * Polynomial.aeval (X k : MvPolynomial K ℚ) P, fun x => ?_⟩
    have hm : ∀ y : K → ℚ, (∀ i, i ≠ k → y i = x i) →
        eval y (monomial (u.erase k) a) = eval x (monomial (u.erase k) a) := by
      intro y hy
      simp only [eval_monomial]
      congr 1
      apply Finsupp.prod_congr
      intro i hi
      rw [Finsupp.support_erase, Finset.mem_erase] at hi
      rw [hy i hi.1]
    have hP' : ∀ y : K → ℚ, eval y (Polynomial.aeval (X k : MvPolynomial K ℚ) P) = P.eval (y k) := by
      intro y
      clear hP
      induction P using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
      | monomial n c => simp [Polynomial.aeval_monomial]
    have hu : monomial u a = monomial (u.erase k) a * X k ^ (u k) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, add_comm, Finsupp.single_add_erase]
    have hy : ∀ i, i ≠ k → (x - Pi.single k (1 : ℚ) : K → ℚ) i = x i := by
      intro i hi
      simp [hi]
    rw [hu, map_mul, map_mul, map_mul, hm _ hy, hP', hP', map_pow, eval_X]
    have hk : (x - Pi.single k (1 : ℚ) : K → ℚ) k = x k - 1 := by simp
    rw [hk]
    linear_combination (eval x (monomial (u.erase k) a)) * hP (x k)
  | add p q hp hq =>
    obtain ⟨R₁, h₁⟩ := hp
    obtain ⟨R₂, h₂⟩ := hq
    exact ⟨R₁ + R₂, fun x => by simp only [map_add]; linear_combination h₁ x + h₂ x⟩

theorem PolyOfDiffsExact.full : PolyOfDiffsExact.Statement := by
  intro K _ _ h hq
  choose q hq using hq
  choose R hR using fun k => exists_mvpoly_backDiff k (q k)

  have step : ∀ k (m : K → ℤ) (t : ℤ),
      h (Function.update m k t) - eval (fun j => ((Function.update m k t j : ℤ) : ℚ)) (R k) =
        h (Function.update m k (t - 1)) - eval (fun j => ((Function.update m k (t - 1) j : ℤ) : ℚ)) (R k) := by
    intro k m t
    have e1 := hq k (Function.update m k t)
    have e2 := hR k (fun j => ((Function.update m k t j : ℤ) : ℚ))
    have s : Function.update m k t - Pi.single k 1 = Function.update m k (t - 1) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
    have s' : (fun j => ((Function.update m k t j : ℤ) : ℚ)) - Pi.single k 1 =
        fun j => ((Function.update m k (t - 1) j : ℤ) : ℚ) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
    rw [s] at e1
    rw [s'] at e2
    linear_combination e1 - e2
  have line : ∀ k (m : K → ℤ) (t : ℤ),
      h (Function.update m k t) - eval (fun j => ((Function.update m k t j : ℤ) : ℚ)) (R k) =
        h (Function.update m k 0) - eval (fun j => ((Function.update m k 0 j : ℤ) : ℚ)) (R k) := by
    intro k m t
    induction t using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [step, add_sub_cancel_right, ih]
    | pred i ih => rw [← ih, step k m (-(i : ℤ))]
  have key : ∀ s : Finset K, ∃ p : MvPolynomial K ℚ, ∀ m : K → ℤ, (∀ j ∉ s, m j = 0) →
      h m = eval (fun j => (m j : ℚ)) p := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C (h 0), fun m hm => ?_⟩
      rw [eval_C]
      congr 1
      funext j
      exact hm j (Finset.notMem_empty j)
    | insert k s hk ih =>
      obtain ⟨p, hp⟩ := ih
      let z : K → MvPolynomial K ℚ := fun j => if j = k then 0 else X j
      refine ⟨bind₁ z p + R k - bind₁ z (R k), fun m hm => ?_⟩
      have hm0 : ∀ j ∉ s, Function.update m k 0 j = 0 := by
        intro j hj
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [Function.update_of_ne hjk]
          exact hm j (by simp [hjk, hj])
      have hz : ∀ P : MvPolynomial K ℚ, eval (fun j => (m j : ℚ)) (bind₁ z P) =
          eval (fun j => ((Function.update m k 0 j : ℤ) : ℚ)) P := by
        intro P
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p j hp =>
          simp only [map_mul, hp, bind₁_X_right, eval_X]
          by_cases hj : j = k
          · subst hj; simp [z]
          · simp [z, hj]
      have e := line k m (m k)
      rw [Function.update_eq_self] at e
      rw [map_sub, map_add, hz, hz, ← hp _ hm0]
      linear_combination e
  obtain ⟨p, hp⟩ := key Finset.univ
  exact ⟨p, fun m => hp m (fun j hj => absurd (Finset.mem_univ j) hj)⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
