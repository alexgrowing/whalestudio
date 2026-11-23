import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BlocksRel

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem nU_mul_nU (b b' : Matrix (Fin n) (Fin n) ℂ) : nU b * nU b' = nU (b + b') := by
  simp only [nU, fromBlocks_multiply]
  congr 1 <;> simp [add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [nU, fromBlocks_one]

def wU (b : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := JJ n * nU b
  inv := nU (-b) * -JJ n
  val_inv := by
    calc JJ n * nU b * (nU (-b) * -JJ n) = JJ n * (nU b * nU (-b)) * -JJ n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nU_mul_nU, add_neg_cancel, nU_zero, Matrix.mul_one, Matrix.mul_neg, JJ_mul_self, neg_neg]
  inv_val := by
    calc nU (-b) * -JJ n * (JJ n * nU b) = -(nU (-b) * (JJ n * JJ n) * nU b) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      _ = 1 := by
          rw [JJ_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, neg_neg, nU_mul_nU, neg_add_cancel, nU_zero]

theorem wU_mem (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : wU b ∈ GR n := by
  change InG (JJ n * nU b)
  have hb' : bᴴ = b := hb
  simp only [InG, JJ, nU, Matrix.conjTranspose_mul, fromBlocks_conjTranspose, fromBlocks_multiply, hb']
  congr 1 <;> simp [hb']

theorem cell_dec (y : GR n) (hc : (mR y).toBlocks₂₁.det ≠ 0) :
    ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧ mR g = JJ n * nU b ∧ y = y₁ * g := by
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hinv : mR y * mR y⁻¹ = 1 := congrArg mR (mul_inv_cancel y)
  have hJ : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have e1 : mR y * JJ n * (mR y)ᴴ * JJ n * mR y = - mR y := by
      calc _ = mR y * JJ n * ((mR y)ᴴ * JJ n * mR y) := by simp only [Matrix.mul_assoc]
        _ = - mR y := by rw [hy, Matrix.mul_assoc, JJ_mul_self, Matrix.mul_neg, Matrix.mul_one]
    have e2 : mR y * JJ n * (mR y)ᴴ * JJ n = -1 := by
      calc _ = mR y * JJ n * (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hinv, Matrix.mul_one]
        _ = -1 := by rw [← Matrix.mul_assoc, e1, Matrix.neg_mul, hinv]
    calc _ = mR y * JJ n * (mR y)ᴴ * (JJ n * -JJ n) := by
          rw [Matrix.mul_neg, JJ_mul_self, neg_neg, Matrix.mul_one]
      _ = JJ n := by rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hrel : (mR y).toBlocks₂₁ * ((mR y).toBlocks₂₂)ᴴ = (mR y).toBlocks₂₂ * ((mR y).toBlocks₂₁)ᴴ := by
    have h22 := congrArg toBlocks₂₂ hJ
    rw [← fromBlocks_toBlocks (mR y)] at h22
    simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h22
    simp at h22
    rw [neg_add_eq_zero] at h22
    exact h22.symm
  have hblk : toBlocks₂₁ (mR y * fromBlocks (-((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) (-1) 1 0) =
      -((mR y).toBlocks₂₁ * ((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) + (mR y).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
  set C := (mR y).toBlocks₂₁ with hCdef
  set D := (mR y).toBlocks₂₂ with hDdef
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hc
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hC.star
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hC, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = C⁻¹ * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCH, Matrix.mul_one]
  let g : GR n := ⟨wU (C⁻¹ * D), wU_mem _ hb⟩
  refine ⟨y * g⁻¹, g, C⁻¹ * D, ?_, hb, rfl, (inv_mul_cancel_right y g).symm⟩
  have hk : nU (-(C⁻¹ * D)) * -JJ n = fromBlocks (-(C⁻¹ * D)) (-1) 1 0 := by
    simp only [nU, JJ, fromBlocks_neg, fromBlocks_multiply]
    congr 1 <;> simp
  have hm : mR (y * g⁻¹) = mR y * (nU (-(C⁻¹ * D)) * -JJ n) := rfl
  show toBlocks₂₁ (mR (y * g⁻¹)) = 0
  rw [hm, hk, hblk, ← Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.one_mul, neg_add_cancel]

theorem conj_cell {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (g : GR n)
    (b : Matrix (Fin n) (Fin n) ℂ) (hg : mR g = JJ n * nU b) (h : ℝ) :
    mR (a h * g * a h) = JJ n * nU (bS X h b) := by
  have h1 := ha h
  unfold IsDil at h1
  have hm : mR (a h * g * a h) = mR (a h) * mR g * mR (a h) := rfl
  rw [hm, h1, hg]
  simp only [JJ, nU, bS, fromBlocks_multiply]
  congr 1 <;> simp [diagonal_mul_diagonal, ← Complex.ofReal_mul, ← Real.exp_add, Matrix.mul_assoc, ← Complex.exp_add]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem cell_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y : GR n)
    (hc : (mR y).toBlocks₂₁.det ≠ 0) (s : ℝ) : (mR (y * a s)).toBlocks₂₁.det ≠ 0 := by
  have h1 := ha s
  unfold IsDil at h1
  have hm : mR (y * a s) = mR y * mR (a s) := rfl
  rw [hm, h1, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero, det_mul, det_diagonal]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem weight_factor_dilation {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (p q : ℕ) (e : ℤ) (h : ℝ) :
    F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ)) := by
  have hm := ha (-h)
  unfold IsDil at hm
  simp only [F0, f0, u1, u2, hm, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, neg_zero, zero_add,
    det_fromBlocks_zero₂₁, det_diagonal, Complex.ofReal_exp]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
