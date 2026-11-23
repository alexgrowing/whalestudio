import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TracePowEqZeroOfLeDim

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section Newton

open Polynomial

private theorem trace_pow_eq_zero_of_le_dim {K : Type*} [Field K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    ∀ k, 1 ≤ k → (N ^ k).trace = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim .. | (apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> first | assumption | infer_instance)

private theorem trace_aeval_X_mul {K : Type*} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) (p : K[X]) :
    (aeval N (X * p)).trace = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, Matrix.trace_add, hp, hq, add_zero]
  | monomial n a =>
    rw [show (X * monomial n a : K[X]) = monomial (n + 1) a by
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]; ring]
    rw [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, h, smul_zero]

private theorem isNilpotent_of_trace_pow_succ {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) : IsNilpotent N := by
  classical
  have hint : IsIntegral K N := Algebra.IsIntegral.isIntegral N
  have hμ : minpoly K N ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K N) hμ 0
  set m := (minpoly K N).rootMultiplicity 0
  simp only [map_zero, sub_zero] at hq hnd
  have hcop : IsCoprime (X ^ (m + 1)) q :=
    ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hnd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hXq : aeval N (X ^ (m + 1) * q) = 0 := by
    rw [show (X ^ (m + 1) * q : K[X]) = X * minpoly K N by rw [hq]; ring, map_mul,
      minpoly.aeval, mul_zero]
  have h1 : aeval N (u * X ^ (m + 1)) + aeval N (v * q) = 1 := by
    rw [← map_add, huv, map_one]
  have hprod : aeval N (u * X ^ (m + 1)) * aeval N (v * q) = 0 := by
    rw [← map_mul, show (u * X ^ (m + 1) * (v * q) : K[X]) = u * v * (X ^ (m + 1) * q) by ring,
      map_mul, hXq, mul_zero]
  set e := aeval N (u * X ^ (m + 1)) with he_def
  have he : IsIdempotentElem e := by
    have : aeval N (v * q) = 1 - e := by rw [← h1]; abel
    rw [this, mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  have hτ : e.trace = 0 := by
    rw [he_def, show (u * X ^ (m + 1) : K[X]) = X * (u * X ^ m) by ring]
    exact trace_aeval_X_mul N h _
  have hle : IsIdempotentElem (Matrix.toLin' e) := by
    have h3 := Matrix.toLin'_mul e e
    rw [he.eq] at h3
    exact h3.symm
  have hl0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hle (by rw [Matrix.trace_toLin'_eq, hτ])
  have he0 : e = 0 := Matrix.toLin'.map_eq_zero_iff.mp hl0
  have hvq : aeval N (v * q) = 1 := by rw [← h1, he0, zero_add]
  refine ⟨m + 1, ?_⟩
  calc N ^ (m + 1) = N ^ (m + 1) * aeval N (v * q) := by rw [hvq, mul_one]
    _ = aeval N (v * (X ^ (m + 1) * q)) := by
        rw [show (v * (X ^ (m + 1) * q) : K[X]) = X ^ (m + 1) * (v * q) by ring,
          map_mul (aeval N) (X ^ (m + 1)), map_pow, aeval_X]
    _ = 0 := by rw [map_mul, hXq, mul_zero]

end Newton

theorem isNilpotent_of_trace_pow {K : Type*} [Field K] [CharZero K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N :=
  isNilpotent_of_trace_pow_succ N fun k => trace_pow_eq_zero_of_le_dim r N h (k + 1) (by omega)

end

end ReciprocityTheory.L2DbarEstimates.Y
