import Mathlib
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open scoped MatrixOrder Matrix.Norms.L2Operator in

theorem exists_scalar_sub_posSemidef {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
  have h1 : (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := A) hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact Matrix.le_iff.1 h
  refine ⟨1 + ‖A‖, by linarith [norm_nonneg A], ?_⟩
  have e : ((1 + ‖A‖ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A =
      1 + (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A) := by
    rw [Complex.coe_smul, add_smul, one_smul, add_sub_assoc]
  rw [e]
  exact Matrix.PosSemidef.one.add h1

theorem gram_det_eq_zero_of_lt_card {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by
  by_contra hd
  have hu : IsUnit (Nᴴ * N) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := (Matrix.rank_mul_le_right Nᴴ N).trans (Matrix.rank_le_card_height N)
  rw [h1, Fintype.card_fin] at h2
  omega

theorem gram_det_mul_le :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) := by
  intro H r a
  obtain ⟨c, hc1, hc⟩ := exists_scalar_sub_posSemidef (aᴴ * a) (Matrix.isHermitian_conjTranspose_mul_self a)
  refine ⟨c ^ r, one_le_pow₀ hc1, ?_⟩
  intro ι _ _ M
  by_cases hι : r < Fintype.card ι
  · rw [gram_det_eq_zero_of_lt_card (a * M) hι, gram_det_eq_zero_of_lt_card M hι]
    simp
  · push Not at hι
    have hP : (Mᴴ * (aᴴ * a) * M).PosSemidef :=
      (Matrix.posSemidef_conjTranspose_mul_self a).conjTranspose_mul_mul_same M
    have hQ : (Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M).PosSemidef := hc.conjTranspose_mul_mul_same M
    obtain ⟨-, hle, -⟩ := H ι _ _ hP hQ
    have hM0 : 0 ≤ (Mᴴ * M).det.re :=
      (H ι _ _ (Matrix.posSemidef_conjTranspose_mul_self M) (Matrix.posSemidef_conjTranspose_mul_self M)).1
    have e1 : (a * M)ᴴ * (a * M) = Mᴴ * (aᴴ * a) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : Mᴴ * (aᴴ * a) * M + Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M = (c : ℂ) • (Mᴴ * M) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [e1]
    refine hle.trans ?_
    rw [e2, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hι) hM0

end GlobalTheory
