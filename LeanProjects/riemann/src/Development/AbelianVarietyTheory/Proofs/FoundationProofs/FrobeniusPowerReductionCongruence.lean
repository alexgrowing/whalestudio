import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem aeval_qq_pow_sub_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (T : Tower p Ωl) (n : ℕ) (f : (O0 p)[X]), f.natDegree < p ^ n → v (aeval (T.qq n) f ^ (p ^ n) - algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i)) < 1 := by
  intro p hp Ωl _ _ _ v hv hvp T n f hf
  classical
  have hpr : p.Prime := hp.out
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hpr.pos n) (by rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : ℕ → integralClosure (O0 p) Ωl := fun i =>
    ⟨algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i, isIntegral_algebraMap.mul (hq.pow i)⟩
  have key : ∀ s : Finset ℕ, ∃ r : integralClosure (O0 p) Ωl,
      (∑ i ∈ s, t i) ^ p ^ n = ∑ i ∈ s, t i ^ p ^ n + p * r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hpr.ne_zero)]⟩
    | insert a s ha ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hpr (t a) (∑ i ∈ s, t i) n
      exact ⟨r + t a * (∑ i ∈ s, t i) * r', by rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]; ring⟩
  obtain ⟨r, hr⟩ := key (Finset.range (p ^ n))
  have term : ∀ i, ((t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) =
      algebraMap (O0 p) Ωl (f.coeff i ^ p ^ n * qO p ^ i) := by
    intro i
    rw [SubmonoidClass.coe_pow, map_mul, map_pow, map_pow]
    show (algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i) ^ p ^ n = _
    rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, GlobalTheory.K5.Basic.qq_pow]
  have e1 : aeval (T.qq n) f = ((∑ i ∈ Finset.range (p ^ n), t i : integralClosure (O0 p) Ωl) : Ωl) := by
    rw [aeval_eq_sum_range' hf]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
  have e2 : algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) =
      ((∑ i ∈ Finset.range (p ^ n), t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) := by
    rw [map_sum, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun i _ => (term i).symm
  have e3 : aeval (T.qq n) f ^ p ^ n - algebraMap (O0 p) Ωl
      (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) = (p : Ωl) * (r : Ωl) := by
    rw [e1, e2, ← SubmonoidClass.coe_pow, hr]
    push_cast
    ring
  rw [e3, map_mul]
  have hr1 : v (r : Ωl) ≤ 1 := (hv _).2 r.2
  calc v (p : Ωl) * v (r : Ωl) ≤ v (p : Ωl) * 1 := by gcongr
    _ = v (p : Ωl) := mul_one _
    _ < 1 := hvp

end GlobalTheory
