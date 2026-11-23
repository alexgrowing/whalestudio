import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
open scoped ComplexOrder Matrix

namespace GlobalTheory.GradedNorm.Comparable

open Matrix ReciprocityTheory.ChartRestriction.G.FD

theorem lminor_eq_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin (n + 1)) :
    lminor M k = (((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE (Nat.le_of_lt_succ k.isLt)))ᴴ * M *
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  rw [lminor]
  congr 1
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem lminor_re {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosDef) (k : Fin (n + 1)) :
    0 < (lminor M k).re ∧ ((lminor M k).re : ℂ) = lminor M k := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 (lminor_pos h k)
  exact ⟨h1, Complex.ext (by simp) (by simp [h2])⟩

theorem abs_log_lminor {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} {m : ℝ} (hm : 1 ≤ m) (hA : A.PosDef) (hB : B.PosDef)
    (h1 : (((m : ℂ) • B) - A).PosSemidef) (h2 : (((m : ℂ) • A) - B).PosSemidef) (k : Fin (n + 1)) :
    |Real.log (lminor A k).re - Real.log (lminor B k).re| ≤ k * Real.log m := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  obtain ⟨a1, -⟩ := lminor_re hA k
  obtain ⟨b1, -⟩ := lminor_re hB k
  have u := GlobalTheory.CompMetric.det_re_le_of_sub hm0.le hA h1
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
  have v := GlobalTheory.CompMetric.det_re_le_of_sub hm0.le hB h2
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
  rw [← lminor_eq_det, ← lminor_eq_det] at u v
  have hpow : 0 < m ^ (k : ℕ) := pow_pos hm0 _
  have lu := Real.log_le_log a1 u
  have lv := Real.log_le_log b1 v
  rw [Real.log_mul hpow.ne' b1.ne', Real.log_pow] at lu
  rw [Real.log_mul hpow.ne' a1.ne', Real.log_pow] at lv
  rw [abs_le]
  constructor <;> linarith

theorem graded_log_bound : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (m : ℝ), 1 ≤ m → A.PosDef → B.PosDef →
    (((m : ℂ) • B) - A).PosSemidef → (((m : ℂ) • A) - B).PosSemidef → ∀ i : Fin n,
    |Real.log (GlobalTheory.GradedNorm.grSq A i) - Real.log (GlobalTheory.GradedNorm.grSq B i)| ≤ 2 * n * Real.log m := by
  intro n A B m hm hA hB h1 h2 i
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  have e : ∀ {M : Matrix (Fin n) (Fin n) ℂ}, M.PosDef →
      Real.log (grSq M i) = Real.log (lminor M i.succ).re - Real.log (lminor M i.castSucc).re := by
    intro M hM
    obtain ⟨p1, p2⟩ := lminor_re hM i.succ
    obtain ⟨q1, q2⟩ := lminor_re hM i.castSucc
    have : grSq M i = (lminor M i.succ).re / (lminor M i.castSucc).re := by
      rw [grSq, ← p2, ← q2, ← Complex.ofReal_div, Complex.ofReal_re]
      simp only [Complex.ofReal_re]
    rw [this, Real.log_div p1.ne' q1.ne']
  rw [e hA, e hB]
  have s := abs_log_lminor hm hA hB h1 h2 i.succ
  have c := abs_log_lminor hm hA hB h1 h2 i.castSucc
  have hs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
  have hc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := Fin.coe_castSucc i
  rw [hs] at s
  rw [hc] at c
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hi' : ((i : ℕ) : ℝ) ≤ n := by linarith
  push_cast at s
  calc _ = |(Real.log (lminor A i.succ).re - Real.log (lminor B i.succ).re) -
        (Real.log (lminor A i.castSucc).re - Real.log (lminor B i.castSucc).re)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ((i : ℕ) + 1) * Real.log m + (i : ℕ) * Real.log m := add_le_add s c
    _ ≤ 2 * n * Real.log m := by nlinarith

end GlobalTheory.GradedNorm.Comparable
