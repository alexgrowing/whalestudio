import Mathlib
import Formalism.PeriodIntegrals.PairValDefs

noncomputable section

open scoped Classical

namespace PI.NRCW

open Formalism.MainNotions.S PI.PairValDefs Matrix

section Mat

variable {K : Type} [Field K] [NumberField K]

theorem isUpUni_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hV : IsUpUni V) :
    IsUpUni (U * V) := by
  intro i j
  constructor
  · intro hji
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hU i k).1 hk, zero_mul]
    · rw [(hV k j).1 (lt_of_lt_of_le hji (not_lt.mp hk)), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hU i i).2 rfl, (hV i i).2 rfl, mul_one]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hU i k).1 h, zero_mul]
      · rw [(hV k i).1 h, mul_zero]
    · simp

theorem sgUp_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hV : IsUpUni V) :
    sgUp (U * V) = sgUp U + sgUp V := by
  unfold sgUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Matrix.mul_apply, Fintype.sum_eq_add a ⟨a.val + 1, h⟩]
    · rw [(hU a a).2 rfl, (hV ⟨a.val + 1, h⟩ ⟨a.val + 1, h⟩).2 rfl, one_mul, mul_one, add_comm]
    · intro e
      rw [Fin.ext_iff] at e
      simp at e
    · rintro x ⟨hxa, hxb⟩
      rcases lt_or_gt_of_ne hxa with hx | hx
      · rw [(hU a x).1 hx, zero_mul]
      · have hne : x.val ≠ a.val + 1 := fun e => hxb (Fin.ext e)
        have hx' : (⟨a.val + 1, h⟩ : Fin N) < x := by
          rw [Fin.lt_def] at hx ⊢
          show a.val + 1 < x.val
          omega
        rw [(hV x ⟨a.val + 1, h⟩).1 hx', mul_zero]
  · simp

theorem sgUp_one {N : ℕ} : sgUp (1 : Matrix (Fin N) (Fin N) K) = 0 := by
  unfold sgUp
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    rw [Fin.ext_iff] at e
    simp at e
  · rfl

theorem isUpUni_one {N : ℕ} : IsUpUni (1 : Matrix (Fin N) (Fin N) K) := by
  intro i j
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h
  exact Matrix.one_apply_eq i

theorem det_upUni {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hU i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl

theorem isUpUni_inv {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 := by
  have hdet : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
  haveI : Invertible U := Matrix.invertibleOfIsUnitDet U hdet
  have htri : (U⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j h => (hU i j).1 h)
  refine ⟨fun i j => ⟨fun h => htri h, fun h => ?_⟩, hmul⟩
  subst h
  have hii := congrFun (congrFun hmul i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (hU i i).2 rfl, one_mul, Matrix.one_apply_eq] at hii
  · exact hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [(hU i k).1 h, zero_mul]
    · rw [htri h, mul_zero]
  · simp

theorem sgUp_inv {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : sgUp U⁻¹ = - sgUp U := by
  obtain ⟨hI, hmul⟩ := isUpUni_inv hU
  have hs := sgUp_mul hU hI
  rw [hmul, sgUp_one] at hs
  linear_combination -hs

variable [StarRing K]

theorem isLoUni_conjTranspose {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : IsLoUni Uᴴ := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.conjTranspose_apply, (hU j i).1 h, star_zero]
  · subst h
    rw [Matrix.conjTranspose_apply, (hU i i).2 rfl, star_one]

theorem sgLo_conjTranspose {N : ℕ} (U : Matrix (Fin N) (Fin N) K) : sgLo Uᴴ = star (sgUp U) := by
  unfold sgLo sgUp
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · exact Matrix.conjTranspose_apply _ _ _
  · rw [star_zero]

def epsM (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem epsM_mul_self (r : ℕ) : (epsM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * epsM r = 1 := by
  rw [epsM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext b
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem zhatOM_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * epsM r := by
  ext a b
  simp only [ZhatOM, epsM, Matrix.mul_diagonal]
  ring

theorem isUpUni_eps {r : ℕ} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hM : IsUpUni M) :
    IsUpUni (epsM r * M * epsM r) := by
  intro i j
  simp only [epsM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [(hM i j).1 h]
    ring
  · subst h
    rw [(hM i i).2 rfl, mul_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgUp_eps {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgUp (epsM r * M * epsM r) = - sgUp M := by
  unfold sgUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · simp only [epsM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hra : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hx : ((-1 : K) ^ (r - (a.val + 1))) * (-1) ^ (r - (a.val + 1)) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    show (-1 : K) ^ (r - a.val) * M a ⟨a.val + 1, h⟩ * (-1) ^ (r - (a.val + 1)) = -M a ⟨a.val + 1, h⟩
    rw [hra, pow_succ]
    linear_combination (-(M a ⟨a.val + 1, h⟩)) * hx
  · simp

theorem core_Z {r : ℕ} (Z₁ Z₂ N M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hN : IsUpUni N) (hM : IsUpUni M)
    (h : Nᴴ * Z₂ = Z₁ * M) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K, IsLoUni A ∧ IsUpUni B ∧
      ZhatOM Z₂ = A * ZhatOM Z₁ * B ∧ sgLo A + sgUp B = -(star (sgUp N) + sgUp M) := by
  obtain ⟨hNi, hNN⟩ := isUpUni_inv hN
  refine ⟨(N⁻¹)ᴴ, epsM r * M * epsM r, isLoUni_conjTranspose hNi, isUpUni_eps hM, ?_, ?_⟩
  · have hinv : (N⁻¹)ᴴ * Nᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hNN, Matrix.conjTranspose_one]
    have hZ2 : Z₂ = (N⁻¹)ᴴ * (Z₁ * M) := by
      rw [← h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    rw [zhatOM_eq, zhatOM_eq, hZ2]
    have hee := epsM_mul_self (K := K) r
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (epsM r) (epsM r), hee, Matrix.one_mul]
  · rw [sgLo_conjTranspose, sgUp_inv hN, sgUp_eps, star_neg]
    ring

end Mat

end PI.NRCW
