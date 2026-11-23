import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

open scoped Matrix.Norms.Operator in

theorem summable_sinhc_series_mat {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  have h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖ :=
    NormedSpace.norm_expSeries_summable' A
  have h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖ :=
    h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)
  refine Summable.of_norm_bounded h1 fun k => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  refine inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ _)

theorem hasSum_shc_series (x : ℝ) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) (shc x) := by
  unfold shc
  split_ifs with hx
  · subst hx
    have := hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0
      (fun k hk => by simp [hk])
    simpa using this
  · have h := (Real.hasSum_sinh x).div_const x
    have e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k))
        = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x := by
      funext k
      rw [pow_succ]
      field_simp
    rw [e]
    exact h

theorem sinhcAd_mulVec_of_sq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ),
    (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  intro p q Y v x h
  have hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h1 := (summable_sinhc_series_mat (adMat Y)).hasSum.map L hL
  have h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v)
      (((shc x : ℝ) : ℂ) • v) := (Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  show (_ • _) *ᵥ v = _
  rw [Matrix.smul_mulVec, hk, smul_smul]
  push_cast
  rfl

end GlobalTheory.PolarU
