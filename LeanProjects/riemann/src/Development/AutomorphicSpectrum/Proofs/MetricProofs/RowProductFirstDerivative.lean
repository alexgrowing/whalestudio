import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem prod_fin_ite_lt {R : Type*} [CommMonoid R] (a b : R) (m N : ℕ) (h : m ≤ N) :
    (∏ r : Fin N, (if (r : ℕ) < m then a else b)) = a ^ m * b ^ (N - m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < m then a else b) (m + j),
    Finset.prod_range_add]
  have h1 : (∏ x ∈ Finset.range m, (if x < m then a else b)) = a ^ m := by
    rw [Finset.prod_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
    simp
  have h2 : (∏ x ∈ Finset.range j, (if m + x < m then a else b)) = b ^ j := by
    rw [Finset.prod_congr rfl (fun x _ => if_neg (by omega))]
    simp
  rw [h1, h2, Nat.add_sub_cancel_left]

theorem rowW_ite (c : Prop) [Decidable c] :
    rowW ![if c then 1 else 0, 0] (if c then 0 else 1) =
      if c then (X (some 0) : MvPolynomial (Option (Fin 2)) ℝ) else X none := by
  split_ifs <;> simp [rowW]

theorem evalW_X_some_zero (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X (some 0)) = rename some (lin3 n₀) := by
  simp [evalW, lin4]

theorem evalW_X_none (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X none) = X none := by
  simp [evalW]

theorem evalW_pderiv_prod_rowW : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  intro d k hk hkd n
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hm : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hm2 : 2 * (t + 1) - 2 = 2 * t := by omega
  have hj : d + 2 - 2 * (t + 1) = d + 1 - (2 * t + 1) := by omega
  have hprod : (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * (t + 1) - 1 then 1 else 0, 0]
        (if (r : ℕ) < 2 * (t + 1) - 1 then 0 else 1)) =
      X (some 0) ^ (2 * t + 1) * X none ^ (d + 1 - (2 * t + 1)) := by
    simp only [rowW_ite, hm]
    exact prod_fin_ite_lt _ _ _ _ (by omega)
  rw [hprod, hm2, hj, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
  have hne : (none : Option (Fin 2)) ≠ some 0 := by simp
  simp only [pderiv_X_self, pderiv_X_of_ne hne, smul_eq_mul, smul_zero, zero_add, mul_zero,
    add_zero, mul_one, Nat.add_sub_cancel, nsmul_eq_mul]
  simp only [map_mul, map_pow, map_natCast, evalW_X_some_zero, evalW_X_none]
  have hc : (C (2 * ((t + 1 : ℕ) : ℝ) - 1) : MvPolynomial (Option (Fin 3)) ℝ) =
      ((2 * t + 1 : ℕ) : MvPolynomial (Option (Fin 3)) ℝ) := by
    rw [← map_natCast (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ)]
    congr 1
    push_cast
    ring
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
