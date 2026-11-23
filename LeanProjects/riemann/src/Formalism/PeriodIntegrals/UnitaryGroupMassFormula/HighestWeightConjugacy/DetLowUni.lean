import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN

noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

def LowUni {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) : Prop := by
  first | exact @Bl.FirstLemmaN.goal1 n L | exact @Bl.FirstLemmaN.goal1 n | exact @Bl.FirstLemmaN.goal1

def UpTri {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → U i j = 0

def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.lastCases (Fin.lastCases e row j) (fun i' => Fin.lastCases (col i') (fun j' => P i' j') j) i

@[simp] theorem blk_cc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk P col row e i.castSucc j.castSucc = P i j := by simp [blk]

@[simp] theorem blk_cl {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk P col row e i.castSucc (Fin.last n) = col i := by simp [blk]

@[simp] theorem blk_lc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk P col row e (Fin.last n) j.castSucc = row j := by simp [blk]

@[simp] theorem blk_ll {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) :
    blk P col row e (Fin.last n) (Fin.last n) = e := by simp [blk]

theorem det_lowUni {n : ℕ} {L : Matrix (Fin n) (Fin n) ℂ} (h : LowUni L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem exists_LU : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ k (hk : k < n), (g.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0) →
    ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g = L * U
  | 0, g, _ => ⟨1, g, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | n + 1, g, hg => by
    set A : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.castSucc Fin.castSucc with hA
    have hAk : ∀ k (hk : k < n), (A.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0 := by
      intro k hk
      have := hg k (by omega)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL', hU', hLU⟩ := exists_LU n A hAk
    have hdetA : A.det ≠ 0 := by
      have := hg n (by omega)
      convert this using 2
      ext i j; rfl
    have hdL : L'.det = 1 := det_lowUni hL'
    have hdU : U'.det ≠ 0 := by
      intro h0; apply hdetA; rw [hLU, Matrix.det_mul, h0, mul_zero]
    have iL : IsUnit L'.det := by rw [hdL]; exact isUnit_one
    have iU : IsUnit U'.det := isUnit_iff_ne_zero.2 hdU
    set c : Fin n → ℂ := fun j => g (Fin.last n) j.castSucc
    set b : Fin n → ℂ := fun i => g i.castSucc (Fin.last n)
    set r : Fin n → ℂ := Matrix.vecMul c U'⁻¹
    set q : Fin n → ℂ := L'⁻¹ *ᵥ b
    refine ⟨blk L' 0 r 1, blk U' q 0 (g (Fin.last n) (Fin.last n) - r ⬝ᵥ q), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL'.2 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hU' i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cl, blk_ll]
          simp [dotProduct]
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cc, blk_ll, blk_lc]
          have : (Matrix.vecMul r U') j = c j := by
            simp only [r, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ iU, Matrix.vecMul_one]
          simp only [Pi.zero_apply, mul_zero, add_zero]
          exact this.symm
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, Pi.zero_apply, zero_mul, add_zero]
          have : (L' *ᵥ q) i = b i := by
            simp only [q, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ iL, Matrix.one_mulVec]
          exact this.symm
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, blk_lc, Pi.zero_apply, zero_mul,
            add_zero]
          rw [← Matrix.mul_apply, ← hLU]; rfl

end PI.UnitaryGroupMassFormula.HwConjInf
