import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

noncomputable section

open Matrix

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

open Formalism.MainNotions.S Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h.symm

theorem brS_add_left (x x' y : S.V) : brS S (x + x') y = brS S x y + brS S x' y := by
  simp [brS]

theorem brS_smul_left (c : E) (x y : S.V) : brS S (c • x) y = c * brS S x y := by
  simp [brS]

theorem brS_sum_left {ι : Type*} (s : Finset ι) (c : ι → E) (x : ι → S.V) (y : S.V) :
    brS S (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * brS S (x i) y := by
  simp [brS, map_sum]

theorem brS_add_right (x y y' : S.V) : brS S x (y + y') = brS S x y + brS S x y' := by
  simp [brS]

theorem brS_smul_right (c : E) (x y : S.V) : brS S x (c • y) = star c * brS S x y := by
  simp [brS, starRingEnd_apply]

theorem brS_sum_right {ι : Type*} (s : Finset ι) (c : ι → E) (x : S.V) (y : ι → S.V) :
    brS S x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, star (c i) * brS S x (y i) := by
  simp [brS, map_sum, starRingEnd_apply]

theorem brS_swap (x y : S.V) : brS S y x = star (brS S x y) := by
  exact hT_swap y x

theorem brS_fvec (F : FlagG S r T) (c b : Fin (r + 1)) :
    brS S (F.fvec c) (F.fvec b) = if c = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  unfold brS
  induction c using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j => simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, hT_swap, F.z_orth]
    | cast j => simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]

variable (F : FlagG S r T) (F' : FlagG S r T')

def omp : S.V := ∑ b, (Zhat F F').adjugate b (Fin.last r) • F'.fvec b

theorem brS_omp_fvec (a : Fin (r + 1)) :
    brS S (omp F F') (F.fvec a) = if a = Fin.last r then (Zhat F F').det else 0 := by
  unfold omp
  rw [brS_sum_left]
  have h := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a) (Fin.last r)
  rw [Matrix.mul_apply] at h
  have h2 : ∀ b, (Zhat F F').adjugate b (Fin.last r) * brS S (F'.fvec b) (F.fvec a)
      = Zhat F F' a b * (Zhat F F').adjugate b (Fin.last r) := fun b => by
    rw [mul_comm]; rfl
  simp_rw [h2, h, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem brS_omp_e (a : Fin r) : brS S (omp F F') (F.e a) = 0 := by
  have h : F.e a = F.fvec (Fin.castSucc a) := by simp [FlagG.fvec]
  rw [h, brS_omp_fvec]
  simp [Fin.castSucc_ne_last]

theorem det_eq_Dl : (Zhat F F').det = Dl F F' (r + 1) := by
  unfold Dl leadMinorE
  rw [dif_pos le_rfl]
  congr 1

theorem pairing_omegaPrime_z : brS S (omp F F') F.z = Dl F F' (r + 1) := by
  have h : F.z = F.fvec (Fin.last r) := by simp [FlagG.fvec]
  rw [h, brS_omp_fvec, if_pos rfl, det_eq_Dl]

theorem adj_last_eq_Dl : (Zhat F F').adjugate (Fin.last r) (Fin.last r) = Dl F F' r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold Dl leadMinorE
  rw [dif_pos (Nat.le_succ r), Fin.succAbove_last]
  have hp : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [hp, one_mul]
  congr 1

theorem brS_omp_f' (b : Fin (r + 1)) :
    brS S (omp F F') (F'.fvec b) = if b = Fin.last r then (Zhat F F').adjugate (Fin.last r) (Fin.last r) * -T' else 0 := by
  unfold omp
  rw [brS_sum_left]
  simp_rw [brS_fvec F']
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb]

theorem brS_omp_omp : brS S (omp F F') (omp F F') = -T' * (Dl F F' r * star (Dl F F' r)) := by
  nth_rewrite 2 [omp]
  rw [brS_sum_right]
  simp_rw [brS_omp_f']
  simp [adj_last_eq_Dl]
  ring

def yv : S.V := T • omp F F' + Dl F F' (r + 1) • F.z

theorem brS_yv_e (a : Fin r) : brS S (yv F F') (F.e a) = 0 := by
  unfold yv
  rw [brS_add_left, brS_smul_left, brS_smul_left, brS_omp_e]
  simp [brS, F.z_orth]

theorem pairing_yVector_z : brS S (yv F F') F.z = 0 := by
  unfold yv
  rw [brS_add_left, brS_smul_left, brS_smul_left, pairing_omegaPrime_z]
  simp [brS, F.z_norm]
  ring

theorem brS_yv_yv (hT : star T = T) : brS S (yv F F') (yv F F') = T * Gflag F F' := by
  have hz : brS S F.z (yv F F') = 0 := by rw [brS_swap, pairing_yVector_z, star_zero]
  have ho : brS S (omp F F') (yv F F') = T * brS S (omp F F') (omp F F') + star (Dl F F' (r + 1)) * Dl F F' (r + 1) := by
    unfold yv
    rw [brS_add_right, brS_smul_right, brS_smul_right, pairing_omegaPrime_z, hT]
  conv_lhs => rw [show yv F F' = T • omp F F' + Dl F F' (r + 1) • F.z from rfl]
  rw [brS_add_left, brS_smul_left, brS_smul_left, ← show yv F F' = T • omp F F' + Dl F F' (r + 1) • F.z from rfl, hz, ho, brS_omp_omp]
  unfold Gflag
  ring

end Formalism.L2.SG.NGCut.NormalVectorPairings
