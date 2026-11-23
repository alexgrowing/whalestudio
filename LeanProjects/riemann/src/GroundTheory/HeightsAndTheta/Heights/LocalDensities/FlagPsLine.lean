import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

theorem sum_fin_split_castLE {M : Type*} [AddCommMonoid M] {i N : ℕ} (hi : i ≤ N)
    (f : Fin N → M) :
    ∑ c, f c = ∑ c : Fin i, f (Fin.castLE hi c) + ∑ c, if i ≤ c.val then f c else 0 := by
  have h1 : (Finset.univ.filter fun c : Fin N => c.val < i) =
      Finset.univ.map (Fin.castLEEmb hi) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨c', rfl⟩; exact c'.isLt
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin N => c.val < i), h1,
    Finset.sum_map, Finset.sum_filter]
  simp only [Fin.castLEEmb_apply, not_lt]

theorem contDiff_det_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Type*} [Fintype m] [DecidableEq m] {M : E → Matrix m m ℂ}
    (h : ∀ a b, ContDiff ℝ 2 fun x => M x a b) : ContDiff ℝ 2 fun x => (M x).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  exact (contDiff_prod fun a _ => h _ _).const_smul _

variable {N : ℕ}

def sigSign (p : ℕ) (a : Fin N) : ℝ := if a.val < p then 1 else -1

theorem signatureForm_eq (p : ℕ) :
    signatureForm N p = diagonal fun a => ((sigSign p a : ℝ) : ℂ) := by
  unfold signatureForm
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

def tailSum (p i : ℕ) (L : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ b : Fin N, ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0

section Poly

variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)

def colPoly : Matrix (Fin N) (Fin i) ℂ[X] :=
  Matrix.of fun c b => (if c = Fin.castLE hi b then 1 else 0) + X * C (L c (Fin.castLE hi b))

def rowPoly : Matrix (Fin i) (Fin N) ℂ[X] :=
  Matrix.of fun a c =>
    (if c = Fin.castLE hi a then 1 else 0) + X * C (star (L c (Fin.castLE hi a)))

def topPoly : Matrix (Fin i) (Fin i) ℂ[X] := (colPoly i hi L).submatrix (Fin.castLE hi) id

def topPoly' : Matrix (Fin i) (Fin i) ℂ[X] := (rowPoly i hi L).submatrix id (Fin.castLE hi)

def sigTop : Matrix (Fin i) (Fin i) ℂ :=
  diagonal fun a => ((sigSign p (Fin.castLE hi a) : ℝ) : ℂ)

def tailForm : Matrix (Fin i) (Fin i) ℂ :=
  Matrix.of fun a b => ∑ c : Fin N, if i ≤ c.val then
    star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi b) else 0

def kerPoly : Matrix (Fin i) (Fin i) ℂ[X] :=
  (sigTop p i hi).map C * (topPoly' i hi L).adjugate * (tailForm p i hi L).map C *
    (topPoly i hi L).adjugate

theorem gram_eq : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
    topPoly' i hi L * (sigTop p i hi).map C * topPoly i hi L +
      (X ^ 2 : ℂ[X]) • (tailForm p i hi L).map C := by
  rw [signatureForm_eq]
  refine Matrix.ext fun a b => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply]
  simp only [Matrix.diagonal_map (map_zero C), Matrix.mul_diagonal]
  rw [sum_fin_split_castLE hi]
  congr 1
  · rw [sigTop, Matrix.diagonal_map (map_zero C), Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rfl
  · simp only [tailForm, Matrix.of_apply, map_sum, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · have h1 : ∀ a : Fin i, c ≠ Fin.castLE hi a := fun a h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp only [rowPoly, colPoly, Matrix.of_apply, h1, if_false, zero_add, map_mul]
      ring
    · simp

theorem sigTop_mul_self : sigTop p i hi * sigTop p i hi = 1 := by
  rw [sigTop, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

variable {L}

theorem det_topPoly (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly i hi L).det = 1 := by
  rw [det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly, colPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have h1 : Fin.castLE hi a ≠ Fin.castLE hi b := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi a) (Fin.castLE hi b) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly, colPoly, h1, h2]

theorem det_topPoly' (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly' i hi L).det = 1 := by
  rw [det_of_isUpperTriangular ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly', rowPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : b < a := by simpa using hab
    have h1 : Fin.castLE hi b ≠ Fin.castLE hi a := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi b) (Fin.castLE hi a) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly', rowPoly, h1, h2]

theorem det_gram (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) :
    (rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L).det =
      C (sigTop p i hi).det * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L).det := by
  have hSS : (sigTop p i hi).map C * (sigTop p i hi).map C = 1 := by
    rw [← Matrix.map_mul, sigTop_mul_self]; simp
  have hK : topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L =
      (tailForm p i hi L).map C := by
    calc topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L
        = (topPoly' i hi L * ((sigTop p i hi).map C * (sigTop p i hi).map C) *
            (topPoly' i hi L).adjugate) * (tailForm p i hi L).map C *
            ((topPoly i hi L).adjugate * topPoly i hi L) := by
          simp only [kerPoly, Matrix.mul_assoc]
      _ = (tailForm p i hi L).map C := by
          rw [hSS, Matrix.mul_one, Matrix.mul_adjugate, Matrix.adjugate_mul, det_topPoly i hi hL,
            det_topPoly' i hi hL, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hfac : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
      topPoly' i hi L * (sigTop p i hi).map C * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L) *
        topPoly i hi L := by
    rw [gram_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, hK]
  rw [hfac, det_mul, det_mul, det_mul, det_topPoly i hi hL, det_topPoly' i hi hL, one_mul,
    mul_one]
  rw [show ((sigTop p i hi).map C).det = C (sigTop p i hi).det from
    ((C : ℂ →+* ℂ[X]).map_det _).symm]

end Poly

theorem coeff_det_one_add_X_sq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ[X]) :
    (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 0 = 1 ∧ (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 1 = 0 ∧
      (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 2 = K.trace.coeff 0 := by
  rw [det_one_add_smul]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_one, ← pow_mul, coeff_mul_X_pow']

end

end GroundTheory.Heights₂.Heights.FourB
