import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NodalCubic

open WeierstrassCurve WeierstrassCurve.Projective in
theorem addXYZ_param {k : Type} [Field k] (u v : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.addXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3] ![v * (1 - v), v ^ 2, (1 - v) ^ 3]
      = (u - v) ^ 3 • ![(u * v) * (1 - u * v), (u * v) ^ 2, (1 - u * v) ^ 3] := by
  ext i
  fin_cases i <;>
    simp [addXYZ, addX, addY, addZ, negAddY, negY] <;> ring

open WeierstrassCurve WeierstrassCurve.Projective in
theorem dblXYZ_param {k : Type} [Field k] (u : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.dblXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3]
      = u ^ 3 • ![(u * u) * (1 - u * u), (u * u) ^ 2, (1 - u * u) ^ 3] := by
  ext i
  fin_cases i <;>
    simp [dblXYZ, dblX, dblY, dblZ, negDblY, negY] <;> ring

theorem eq_of_param_equiv {k : Type} [Field k] {u v : k} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∃ c : kˣ, c • ![v * (1 - v), v ^ 2, (1 - v) ^ 3] = ![u * (1 - u), u ^ 2, (1 - u) ^ 3]) :
    u = v := by
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp [Units.smul_def] at h0 h1
  have h2 : (c : k) * v = u := by linear_combination h0 + h1
  have h3 : u * v = u * u := by linear_combination h1 - v * h2
  exact (mul_left_cancel₀ hu h3).symm

open WeierstrassCurve WeierstrassCurve.Projective in
theorem nonsingular_iff_nodal {k : Type} [Field k] (P : Fin 3 → k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P ↔
      P 1 ^ 2 * P 2 + P 0 * P 1 * P 2 = P 0 ^ 3 ∧
        (P 1 * P 2 ≠ 3 * P 0 ^ 2 ∨ 2 * P 1 * P 2 + P 0 * P 2 ≠ 0 ∨ P 1 ^ 2 + P 0 * P 1 ≠ 0) := by
  rw [nonsingular_iff, equation_iff]
  simp [sub_eq_zero]

theorem nonsingular_points : ∀ (k : Type) [Field k], (∀ u : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3]) ∧ (∀ u v : kˣ, ∃ c : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.add ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3] ![(v : k) * (1 - v), (v : k) ^ 2, (1 - (v : k)) ^ 3] = (c : k) • ![((u * v : kˣ) : k) * (1 - (u * v : kˣ)), ((u * v : kˣ) : k) ^ 2, (1 - ((u * v : kˣ) : k)) ^ 3]) ∧ ∀ P : Fin 3 → k, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P → P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ ∃ c : kˣ, P = (c : k) • ![(P 1 / (P 0 + P 1)) * (1 - P 1 / (P 0 + P 1)), (P 1 / (P 0 + P 1)) ^ 2, (1 - P 1 / (P 0 + P 1)) ^ 3] := by
  intro k _
  refine ⟨fun u => ?_, fun u v => ?_, fun P hP => ?_⟩
  · rw [nonsingular_iff_nodal]
    refine ⟨by simp; ring, Or.inr (Or.inr ?_)⟩
    have : ((u : k) ^ 2) ^ 2 + (u : k) * (1 - u) * (u : k) ^ 2 = (u : k) ^ 3 := by ring
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, this]
    exact pow_ne_zero 3 u.ne_zero
  · by_cases h : (u : k) = v
    · refine ⟨u ^ 3, ?_⟩
      rw [Units.val_mul, ← h, WeierstrassCurve.Projective.add_self, dblXYZ_param, Units.val_pow_eq_pow_val]
    · refine ⟨Units.mk0 (((u : k) - v) ^ 3) (pow_ne_zero 3 (sub_ne_zero.mpr h)), ?_⟩
      rw [WeierstrassCurve.Projective.add_of_not_equiv
        (fun h' => h (eq_of_param_equiv u.ne_zero v.ne_zero h')), addXYZ_param, Units.val_mul, Units.val_mk0]
  · rw [nonsingular_iff_nodal] at hP
    obtain ⟨he, hn⟩ := hP
    have key : P 1 * (P 0 + P 1) ≠ 0 := by
      intro h0
      have hx : P 0 = 0 := by
        have : P 0 ^ 3 = 0 := by linear_combination P 2 * h0 - he
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hy : P 1 = 0 := by
        rw [hx, zero_add] at h0
        exact mul_self_eq_zero.mp h0
      simp [hx, hy] at hn
    have hy : P 1 ≠ 0 := left_ne_zero_of_mul key
    have hs : P 0 + P 1 ≠ 0 := right_ne_zero_of_mul key
    refine ⟨hy, hs, Units.mk0 ((P 0 + P 1) ^ 2 / P 1) (div_ne_zero (pow_ne_zero 2 hs) hy), ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      ring
    · simp
      field_simp
    · simp
      field_simp
      linear_combination he

end GlobalTheory.NodalCubic
