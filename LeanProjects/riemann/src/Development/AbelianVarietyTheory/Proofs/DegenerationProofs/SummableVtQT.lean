import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_vt_QT_le (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) :
    ‖N.vt p.1.2 χ‖ ≤ Real.exp (-((q (p.1.1.toAdd + k • χ) - q p.1.1.toAdd) / (k : ℝ) ^ 2)) := by
  rw [NumD.vt]
  simp only [Units.val_mul, norm_mul, h.ψ, h.norm_rep_generators_eq_exp p hk]
  refine (mul_le_of_le_one_right (by positivity) (h.th _)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have e : q (p.1.1.toAdd + k • χ) =
      q p.1.1.toAdd + (k : ℝ) ^ 2 * q χ + k * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (k • χ) = k * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (k • χ) = (k : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [e]
  field_simp
  ring

theorem tendsto_vt_QT (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) :
    Filter.Tendsto (N.vt p.1.2) Filter.cofinite (nhds 0) := by
  have inj : Function.Injective fun χ : N.X => p.1.1.toAdd + k • χ := fun a b e => by
    have e' : k • a = k • b := add_left_cancel e
    rw [← natCast_zsmul, ← natCast_zsmul] at e'
    exact smul_right_injective N.X (Int.natCast_ne_zero.2 hk) e'
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have kp : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) 2
  have t₂ := (Filter.tendsto_atTop_add_const_right _ (-q p.1.1.toAdd) t₁).atTop_div_const kp
  have t₃ := Real.tendsto_exp_neg_atTop_nhds_zero.comp t₂
  refine squeeze_zero_norm (h.norm_vt_QT_le hk p) ?_
  simpa only [Function.comp_def, sub_eq_add_neg] using t₃

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem summable_vt_QT : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) :=
  fun _ _ _ _ _ _ h _ hk p =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (h.tendsto_vt_QT hk p)
end GlobalTheory.Ex
