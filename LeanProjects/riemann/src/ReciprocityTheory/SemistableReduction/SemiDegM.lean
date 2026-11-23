import ReciprocityTheory.SemistableReduction.SemiDegI

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def colMat {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) K :=
  Matrix.of fun a i => b i a

theorem hGram_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : hGram S b = ((colMat b).map S.c)ᵀ * S.G * colMat b := by
  ext i j
  simp only [hGram, HermForm.h, colMat, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem colMat_mulVec {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    colMat b *ᵥ t = ∑ j, t j • b j := by
  funext a
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem form_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (t : Fin k → K) :
    (fun i => S.c (t i)) ⬝ᵥ (hGram S b *ᵥ t) = S.h (colMat b *ᵥ t) (colMat b *ᵥ t) := by
  rw [hGram_eq, hermForm_h_eq]
  simp only [formM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl

theorem hermForm_swap {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.c (S.h x y) = S.h y x := by
  simp only [HermForm.h, map_sum, map_mul, S.c_invol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [S.G_herm]
  ring

theorem quad_eq {r k : ℕ} (E : Matrix (Fin r) (Fin k) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin k → ℂ) : star v ⬝ᵥ ((Eᴴ * X * E) *ᵥ v) = star (E *ᵥ v) ⬝ᵥ (X *ᵥ (E *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

theorem quad_diag {r : ℕ} (d w : Fin r → ℂ) :
    star w ⬝ᵥ (diagonal d *ᵥ w) = ∑ a, d a * ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul', Complex.star_def]
  ring

def midG {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun a => if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0

def midForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := midG r m g
  G_herm a b := by
    by_cases hab : a = b
    · subst hab
      simp only [midG, Matrix.diagonal_apply_eq]
      split_ifs with h
      · exact hfix a h.1 h.2
      · exact map_zero _
    · simp [midG, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
