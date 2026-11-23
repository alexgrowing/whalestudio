import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RootCoordinateFrames

noncomputable section

open Matrix
open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.RealObj.ThreeBlockFrameInverses

section Gen

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem frame_unit (J : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) ι ℂ) (K : Matrix ι (Fin n) ℂ)
    (G M : Matrix ι ι ℂ) (hJh : Jᴴ = J) (hG : Gᴴ = G) (hKΦ : K * Φ = 1) (hΦJ : Φᴴ * J = G * K)
    (hM : Mᴴ * G * M = G) :
    (1 + Φ * (M - 1) * K)ᴴ * J * (1 + Φ * (M - 1) * K) = J := by
  obtain ⟨N, hN0⟩ : ∃ N, N = M - 1 := ⟨_, rfl⟩
  rw [← hN0]
  have hM' : M = 1 + N := by rw [hN0]; abel
  have hJΦ : J * Φ = Kᴴ * G := by
    have h1 := congrArg Matrix.conjTranspose hΦJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, hG] at h1
    exact h1
  have hN : G * N + Nᴴ * G + Nᴴ * G * N = 0 := by
    rw [hM', Matrix.conjTranspose_add, Matrix.conjTranspose_one] at hM
    have h2 : (1 + Nᴴ) * G * (1 + N) = G + (G * N + Nᴴ * G + Nᴴ * G * N) := by noncomm_ring
    rw [h2] at hM
    exact add_left_cancel (hM.trans (add_zero G).symm)
  have hΦJr : ∀ T : Matrix (Fin n) (Fin n) ℂ, Φᴴ * (J * T) = G * (K * T) := by
    intro T
    rw [← Matrix.mul_assoc, hΦJ, Matrix.mul_assoc]
  have hKΦr : ∀ T : Matrix ι (Fin n) ℂ, K * (Φ * T) = T := by
    intro T
    rw [← Matrix.mul_assoc, hKΦ, Matrix.one_mul]
  have hS : (1 + Φ * N * K)ᴴ = 1 + Kᴴ * (Nᴴ * Φᴴ) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have eXJ : Kᴴ * (Nᴴ * Φᴴ) * J = Kᴴ * (Nᴴ * G) * K := by
    simp only [Matrix.mul_assoc]
    rw [hΦJ]
  have eJY : J * (Φ * N * K) = Kᴴ * (G * N) * K := by
    simp only [← Matrix.mul_assoc]
    rw [hJΦ]
  have eXJY : Kᴴ * (Nᴴ * Φᴴ) * J * (Φ * N * K) = Kᴴ * (Nᴴ * G * N) * K := by
    simp only [Matrix.mul_assoc]
    rw [hΦJr, hKΦr]
  have expand : (1 + Kᴴ * (Nᴴ * Φᴴ)) * J * (1 + Φ * N * K) =
      J + Kᴴ * (Nᴴ * Φᴴ) * J + J * (Φ * N * K) + Kᴴ * (Nᴴ * Φᴴ) * J * (Φ * N * K) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  have final : Kᴴ * (Nᴴ * G) * K + Kᴴ * (G * N) * K + Kᴴ * (Nᴴ * G * N) * K = 0 := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add]
    have h3 : Nᴴ * G + G * N + Nᴴ * G * N = 0 := by
      rw [← hN]
      abel
    rw [h3, Matrix.mul_zero, Matrix.zero_mul]
  rw [hS, expand, eXJY, eXJ, eJY]
  calc J + Kᴴ * (Nᴴ * G) * K + Kᴴ * (G * N) * K + Kᴴ * (Nᴴ * G * N) * K
      = J + (Kᴴ * (Nᴴ * G) * K + Kᴴ * (G * N) * K + Kᴴ * (Nᴴ * G * N) * K) := by abel
    _ = J := by rw [final, add_zero]

theorem frame_mul (Φ : Matrix (Fin n) ι ℂ) (K : Matrix ι (Fin n) ℂ) (M : Matrix ι ι ℂ) (hKΦ : K * Φ = 1) :
    (1 + Φ * (M - 1) * K) * Φ = Φ * M := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hKΦ, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem frame_sub (Φ : Matrix (Fin n) ι ℂ) (K : Matrix ι (Fin n) ℂ) (M : Matrix ι ι ℂ) (hKΦ : K * Φ = 1) :
    (1 + Φ * (M - 1) * K - 1) * Φ * K = 1 + Φ * (M - 1) * K - 1 := by
  have e : (1 + Φ * (M - 1) * K - 1 : Matrix (Fin n) (Fin n) ℂ) = Φ * (M - 1) * K := by abel
  rw [e, Matrix.mul_assoc (Φ * (M - 1)) K Φ, hKΦ, Matrix.mul_one]

theorem left_inverse_three_blocks (G G' : Matrix ι ι ℂ) (B : Matrix ι (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ) (h : G * G' = 1) :
    B * C = G * (G' * B * C) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

end Gen

section Blocks

variable {r : ℕ}

def Pl (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := diagonal fun i => if i = Fin.last r then 1 else 0

def Em (r : ℕ) : Matrix (Fin (r + 1)) (Fin r) ℂ := of fun i b => if i = Fin.castSucc b then 1 else 0

theorem last_ne (b : Fin r) : Fin.last r ≠ Fin.castSucc b := (Fin.castSucc_lt_last b).ne'

theorem Pl_mul_Em : Pl r * Em r = 0 := by
  ext i b
  unfold Pl Em
  rw [Matrix.diagonal_mul]
  by_cases h1 : i = Fin.last r
  · subst h1
    simp [last_ne b]
  · simp [h1]

theorem EmT_mul_Pl : (Em r)ᵀ * Pl r = 0 := by
  ext b j
  unfold Pl Em
  rw [Matrix.mul_diagonal]
  by_cases h1 : j = Fin.last r
  · subst h1
    simp [last_ne b]
  · simp [h1]

theorem Pl_mul_Pl : Pl r * Pl r = Pl r := by
  unfold Pl
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem Pl_conjT : (Pl r)ᴴ = Pl r := by
  unfold Pl
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem Em_conjT : (Em r)ᴴ = (Em r)ᵀ := by
  ext b i
  simp only [Em, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem EmT_conjT : ((Em r)ᵀ)ᴴ = Em r := by
  rw [← Em_conjT, Matrix.conjTranspose_conjTranspose]

theorem EmT_mul_Em : (Em r)ᵀ * Em r = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Em, Matrix.mul_apply]
  · simp [Em, Matrix.mul_apply, Matrix.one_apply, Fin.castSucc_inj, h, Ne.symm h]

theorem Em_mul_EmT : Em r * (Em r)ᵀ = 1 - Pl r := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Em, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
    Pl, Matrix.diagonal_apply]
  by_cases hi : i = Fin.last r
  · subst hi
    simp [last_ne]
  · obtain ⟨b, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    by_cases hj : j = Fin.last r
    · subst hj
      simp [(last_ne b).symm, last_ne]
    · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hj
      simp [Fin.castSucc_inj, (last_ne b).symm]

def Gm (t : ℂ) : Matrix (Fin (r + 1) ⊕ Fin r) (Fin (r + 1) ⊕ Fin r) ℂ := fromBlocks (t • Pl r) (Em r) (Em r)ᵀ 0

theorem Gm_mul (s u : ℂ) (h : s * u = 1) : Gm (r := r) s * Gm u = 1 := by
  unfold Gm
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1
  · rw [Matrix.smul_mul, Matrix.mul_smul, Pl_mul_Pl, smul_smul, h, one_smul, Em_mul_EmT]
    abel
  · rw [Matrix.smul_mul, Pl_mul_Em, smul_zero, Matrix.mul_zero, add_zero]
  · rw [Matrix.mul_smul, EmT_mul_Pl, smul_zero, Matrix.zero_mul, add_zero]
  · rw [EmT_mul_Em, Matrix.zero_mul, add_zero]

variable {P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}

theorem lo_last (hP : Formalism.MainNotions.S.IsLoUni P) (i : Fin (r + 1)) :
    P i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  by_cases hi : i = Fin.last r
  · subst hi
    rw [if_pos rfl]
    exact (hP _ _).2 rfl
  · rw [if_neg hi]
    exact (hP _ _).1 (lt_of_le_of_ne (Fin.le_last i) hi)

theorem Pbar_mul_Pl (hP : Formalism.MainNotions.S.IsLoUni P) : P.map star * Pl r = Pl r := by
  ext i j
  unfold Pl
  rw [Matrix.mul_diagonal]
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    rw [lo_last hP]
    split_ifs <;> simp_all
  · simp only [hj, if_false, mul_zero]
    split_ifs <;> simp_all

theorem Pl_mul_PT (hP : Formalism.MainNotions.S.IsLoUni P) : Pl r * Pᵀ = Pl r := by
  ext i j
  unfold Pl
  rw [Matrix.diagonal_mul]
  simp only [Matrix.transpose_apply, Matrix.diagonal_apply]
  by_cases hi : i = Fin.last r
  · subst hi
    rw [lo_last hP]
    by_cases hj : j = Fin.last r
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · simp only [hi, if_false, zero_mul]
    clear hP
    split_ifs <;> simp_all

theorem det_Pbar (hP : Formalism.MainNotions.S.IsLoUni P) : (P.map star).det = 1 := by
  have hd : ∀ i, P i i = 1 := fun i => (hP i i).2 rfl
  rw [Matrix.det_of_lowerTriangular]
  · simp [Matrix.map_apply, hd]
  · intro i j hij
    simp only [Matrix.map_apply]
    rw [(hP i j).1 (OrderDual.toDual_lt_toDual.1 hij), star_zero]

def Rm (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin r) ℂ := (P.map star)⁻¹ * Em r

def Ym (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin r) (Fin r) ℂ := (Em r)ᵀ * Rm P

def Cm (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin r) (Fin r) ℂ := (Rm P)ᴴ * Pl r * Rm P

def isotropicCorrectionMatrix (t : ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (-(2 * t)⁻¹) • (((Em r)ᵀ * P.map star * Em r)ᴴ * Cm P)

def Xm (t : ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin r) ℂ :=
  Em r * isotropicCorrectionMatrix t P + t⁻¹ • (Pl r * Rm P)

def Mm (t : ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Matrix (Fin (r + 1) ⊕ Fin r) (Fin (r + 1) ⊕ Fin r) ℂ :=
  fromBlocks Pᵀ (Xm t P) 0 (Ym P)

theorem Mm_gram (hP : Formalism.MainNotions.S.IsLoUni P) {t : ℂ} (ht : t ≠ 0) (hts : star t = t) :
    (Mm t P)ᴴ * Gm t * Mm t P = Gm t := by
  have hPT : (Pᵀ)ᴴ = P.map star := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hPbH : (P.map star)ᴴ = Pᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hti : star t⁻¹ = t⁻¹ := by simp [hts]
  have hc2 : star (-(2 * t)⁻¹) = -(2 * t)⁻¹ := by simp [hts]
  have hdetU : IsUnit (P.map star).det := by
    rw [det_Pbar hP]
    exact isUnit_one
  have hPR : P.map star * Rm P = Em r := by
    unfold Rm
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetU, Matrix.one_mul]
  have hC : (Cm P)ᴴ = Cm P := by
    unfold Cm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Pl_conjT,
      Matrix.mul_assoc]
  have hPlX : Pl r * Xm t P = t⁻¹ • (Pl r * Rm P) := by
    unfold Xm
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Pl_mul_Em, Matrix.zero_mul, zero_add, Matrix.mul_smul,
      ← Matrix.mul_assoc, Pl_mul_Pl]
  have hEX : (Em r)ᵀ * Xm t P = isotropicCorrectionMatrix t P := by
    unfold Xm
    rw [Matrix.mul_add, ← Matrix.mul_assoc, EmT_mul_Em, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      EmT_mul_Pl, Matrix.zero_mul, smul_zero, add_zero]
  have hF7 : ((Em r)ᵀ * P.map star * Em r) * Ym P = 1 := by
    unfold Ym
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Em r), Em_mul_EmT, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, hPR, ← Matrix.mul_assoc (P.map star) (Pl r), Pbar_mul_Pl hP, Matrix.mul_sub, EmT_mul_Em,
      ← Matrix.mul_assoc, EmT_mul_Pl, Matrix.zero_mul, sub_zero]
  have hXPR : (Xm t P)ᴴ * (Pl r * Rm P) = t⁻¹ • Cm P := by
    have h1 : (Rm P)ᴴ * Pl r * Xm t P = t⁻¹ • Cm P := by
      unfold Cm
      rw [Matrix.mul_assoc, hPlX, Matrix.mul_smul, ← Matrix.mul_assoc]
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Pl_conjT, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, hC, hti] at h2
    exact h2
  have ha : (Xm t P)ᴴ * (t • Pl r) * Xm t P = t⁻¹ • Cm P := by
    rw [Matrix.mul_assoc, Matrix.smul_mul, hPlX, smul_smul, mul_inv_cancel₀ ht, one_smul, hXPR]
  have hb : (Ym P)ᴴ * (Em r)ᵀ * Xm t P = (Ym P)ᴴ * isotropicCorrectionMatrix t P := by
    rw [Matrix.mul_assoc, hEX]
  have hcc : (Xm t P)ᴴ * Em r * Ym P = (isotropicCorrectionMatrix t P)ᴴ * Ym P := by
    rw [← hEX, Matrix.conjTranspose_mul, EmT_conjT]
  have hYX : (Ym P)ᴴ * isotropicCorrectionMatrix t P = (-(2 * t)⁻¹) • Cm P := by
    unfold isotropicCorrectionMatrix
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF7, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hXY : (isotropicCorrectionMatrix t P)ᴴ * Ym P = (-(2 * t)⁻¹) • Cm P := by
    have h := congrArg Matrix.conjTranspose hYX
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul, hC, hc2] at h
    exact h
  have h12 : P.map star * (t • Pl r) * Xm t P + P.map star * Em r * Ym P = Em r := by
    have e1 : P.map star * (t • Pl r) * Xm t P = Pl r * Rm P := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hPlX, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ ht, one_smul, ← Matrix.mul_assoc, Pbar_mul_Pl hP]
    have e2 : P.map star * Em r * Ym P = Em r - Pl r * Rm P := by
      unfold Ym
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Em r), Em_mul_EmT, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        hPR, ← Matrix.mul_assoc, Pbar_mul_Pl hP]
    rw [e1, e2]
    abel
  have hM : (Mm t P)ᴴ = Matrix.fromBlocks (P.map star) 0 (Xm t P)ᴴ (Ym P)ᴴ := by
    unfold Mm
    rw [Matrix.fromBlocks_conjTranspose, hPT, Matrix.conjTranspose_zero]
  rw [hM]
  unfold Gm Mm
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · rw [Matrix.mul_smul, Matrix.smul_mul, Pbar_mul_Pl hP, Pl_mul_PT hP]
  · have h21 := congrArg Matrix.conjTranspose h12
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hts, Pl_conjT,
      Em_conjT, hPbH, Matrix.mul_assoc] at h21
    rw [Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    exact h21
  · rw [Matrix.add_mul, ha, hb, hcc, hYX, hXY]
    have hz : t⁻¹ + -(2 * t)⁻¹ + -(2 * t)⁻¹ = 0 := by
      field_simp
      ring
    rw [← add_smul, ← add_smul, hz, zero_smul]

end Blocks

section Main

variable {n r : ℕ}

theorem castSucc_ne (b : Fin r) : Fin.castSucc b ≠ Fin.last r := (Fin.castSucc_lt_last b).ne

theorem hJ_swap (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  show hJ ε x y = (starRingEnd ℂ) (hJ ε y x)
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp <;> ring

def Sm {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : Matrix (Fin n) ι ℂ) (K : Matrix ι (Fin n) ℂ)
    (M : Matrix ι ι ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Φ * (M - 1) * K

def Phi (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin (r + 1) ⊕ Fin r) ℂ :=
  of fun k i => Sum.elim (fam e z) f i k

def Km (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℂ) :
    Matrix (Fin (r + 1) ⊕ Fin r) (Fin n) ℂ :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (@HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Gm (r := r) t⁻¹) (Phi e f z).conjTranspose)
    (Formalism.REAL.Jm ε)

theorem Phi_mulVec (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin (r + 1) ⊕ Fin r → ℂ) :
    Phi e f z *ᵥ w = ∑ c, w (Sum.inl c) • fam e z c + ∑ b, w (Sum.inr b) • f b := by
  funext k
  simp [Matrix.mulVec, dotProduct, Phi, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]

theorem PhiJ_mulVec (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (y : Fin n → ℂ) :
    ((Phi e f z)ᴴ * Formalism.REAL.Jm ε) *ᵥ y = fun i => hJ ε (Sum.elim (fam e z) f i) y := by
  rw [← Matrix.mulVec_mulVec]
  funext i
  simp only [hJ, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Phi, Matrix.of_apply, Pi.star_apply]

theorem PhiJPhi_apply (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (i j : Fin (r + 1) ⊕ Fin r) :
    ((Phi e f z)ᴴ * Formalism.REAL.Jm ε * Phi e f z) i j =
      hJ ε (Sum.elim (fam e z) f i) (Sum.elim (fam e z) f j) := by
  have h := congrFun (PhiJ_mulVec ε e f z (Sum.elim (fam e z) f j)) i
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Phi, Matrix.of_apply]

theorem gram (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) :
    (Phi e f z)ᴴ * Formalism.REAL.Jm ε * Phi e f z = Gm (hJ ε z z) := by
  ext i j
  rw [PhiJPhi_apply]
  rcases i with c | b <;> rcases j with c' | b'
  · simp only [Sum.elim_inl, Gm, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Pl, Matrix.diagonal_apply, smul_eq_mul]
    induction c using Fin.lastCases with
    | last =>
      induction c' using Fin.lastCases with
      | last => simp [fam]
      | cast a => simp [fam, hJ_swap ε z (e a), (hez a).1, last_ne a]
    | cast a =>
      induction c' using Fin.lastCases with
      | last => simp [fam, (hez a).1, castSucc_ne a]
      | cast a' => simp [fam, hee a a', castSucc_ne a]
  · simp only [Sum.elim_inl, Sum.elim_inr, Gm, Matrix.fromBlocks_apply₁₂, Em, Matrix.of_apply]
    induction c using Fin.lastCases with
    | last => simp [fam, hJ_swap ε z (f b'), (hez b').2, last_ne b']
    | cast a => simp [fam, hef a b', Fin.castSucc_inj]
  · simp only [Sum.elim_inl, Sum.elim_inr, Gm, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, Em, Matrix.of_apply]
    induction c' using Fin.lastCases with
    | last => simp [fam, (hez b).2, last_ne b]
    | cast a =>
      simp only [fam, Fin.snoc_castSucc]
      rw [hJ_swap ε (f b) (e a), hef a b]
      by_cases hab : a = b
      · subst hab
        simp
      · simp [hab, Fin.castSucc_inj]
  · simp only [Sum.elim_inr, Gm, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    exact hff b b'

theorem Gm_conjT {t : ℂ} (hts : star t = t) : (Gm (r := r) t)ᴴ = Gm t := by
  unfold Gm
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul, hts, Pl_conjT, EmT_conjT, Em_conjT,
    Matrix.conjTranspose_zero]

theorem Gm_mulVec_inr (s : ℂ) (w : Fin (r + 1) ⊕ Fin r → ℂ) (b : Fin r) :
    (Gm s *ᵥ w) (Sum.inr b) = w (Sum.inl (Fin.castSucc b)) := by
  simp [Gm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Em]

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := Submodule.span_mono (fun _ ⟨b, hb, hy⟩ => ⟨b, lt_of_lt_of_le hb h, hy⟩)

theorem lo_sum_mem {P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hP : Formalism.MainNotions.S.IsLoUni P)
    (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin (r + 1)) :
    ∑ c, P a c • fam e z c - fam e z a ∈ spanLt e a.1 := by
  classical
  have key : ∑ c, P a c • fam e z c - fam e z a = ∑ c ∈ Finset.univ.filter (fun c => c < a), P a c • fam e z c := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => c < a)]
    have hrest : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < a), P a c • fam e z c = fam e z a := by
      rw [Finset.sum_eq_single a]
      · rw [(hP a a).2 rfl, one_smul]
      · intro c hc hca
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hc
        rw [(hP a c).1 (lt_of_le_of_ne hc (Ne.symm hca)), zero_smul]
      · intro ha
        simp at ha
    rw [hrest, add_sub_cancel_right]
  rw [key]
  refine Submodule.sum_mem _ (fun c hc => Submodule.smul_mem _ _ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  have hcl : c ≠ Fin.last r := fun h => by
    rw [h] at hc
    exact absurd hc (not_lt.2 (Fin.le_last a))
  obtain ⟨b, rfl⟩ := Fin.exists_castSucc_eq.2 hcl
  simp only [fam, Fin.snoc_castSucc]
  apply Submodule.subset_span
  exact ⟨b, by simpa [Fin.lt_def] using hc, rfl⟩

theorem NRealize_holds : RootCoordinateFrames.NRealize := by
  intro n r ε e f z hee hff hef hez hzz P hP
  have hts : star (hJ ε z z) = hJ ε z z := (hJ_swap ε z z).symm
  have hgram := gram ε e f z hee hff hef hez
  have hKΦ : Km ε e f z (hJ ε z z) * Phi e f z = 1 := by
    rw [Km, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Phi e f z).conjTranspose, hgram,
      Gm_mul _ _ (inv_mul_cancel₀ hzz)]
  have hΦJ : (Phi e f z)ᴴ * Formalism.REAL.Jm ε = Gm (hJ ε z z) * Km ε e f z (hJ ε z z) := by
    exact left_inverse_three_blocks (Gm (hJ ε z z)) (Gm (hJ ε z z)⁻¹) _ _ (Gm_mul _ _ (mul_inv_cancel₀ hzz))
  have hSJ : (Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P))ᴴ * Formalism.REAL.Jm ε *
      Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P) = Formalism.REAL.Jm ε :=
    frame_unit _ _ _ _ _ (Formalism.REAL.Jm_conjTranspose ε) (Gm_conjT hts) hKΦ hΦJ (Mm_gram hP hzz hts)
  have hSΦ : Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P) * Phi e f z =
      Phi e f z * Mm (hJ ε z z) P := frame_mul _ _ _ hKΦ
  have hS1 : (Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P) - 1) * Phi e f z *
      Km ε e f z (hJ ε z z) = Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P) - 1 :=
    frame_sub _ _ _ hKΦ
  set S := Sm (Phi e f z) (Km ε e f z (hJ ε z z)) (Mm (hJ ε z z) P) with hSdef
  have hl : (Formalism.REAL.Jm ε * Sᴴ * Formalism.REAL.Jm ε) * S = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ, hSJ, Formalism.REAL.Jm_mul_self]
  have hr : S * (Formalism.REAL.Jm ε * Sᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mpr hl
  have hfam : ∀ a, S *ᵥ fam e z a = ∑ c, P a c • fam e z c := by
    intro a
    have h1 : fam e z a = Phi e f z *ᵥ Pi.single (Sum.inl a) 1 := by
      rw [Phi_mulVec]; simp [Pi.single_apply]
    rw [h1, mulVec_mulVec, hSΦ, ← mulVec_mulVec, mulVec_single_one, Phi_mulVec]
    simp [Mm, col]
  have hmem : ∀ a : Fin (r + 1), (S - 1) *ᵥ fam e z a ∈ spanLt e a.1 := by
    intro a; rw [sub_mulVec, one_mulVec, hfam]; exact lo_sum_mem hP e z a
  refine ⟨⟨⟨S, Formalism.REAL.Jm ε * Sᴴ * Formalism.REAL.Jm ε, hr, hl⟩, hSJ⟩, ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩, hfam⟩
  · have := hmem (Fin.castSucc a); simpa [fam] using this
  · have := hmem (Fin.last r); simpa [fam] using this
  · show (S - 1) *ᵥ y ∈ spanLt e r
    have hK : (S - 1) *ᵥ y = (S - 1) *ᵥ (Phi e f z *ᵥ (Km ε e f z (hJ ε z z) *ᵥ y)) := by
      rw [mulVec_mulVec, mulVec_mulVec, hS1]
    have hv : ∀ b, (Km ε e f z (hJ ε z z) *ᵥ y) (Sum.inr b) = 0 := by
      intro b
      rw [Km, Matrix.mul_assoc, ← mulVec_mulVec, Gm_mulVec_inr, PhiJ_mulVec]
      simp [fam, hy b]
    rw [hK, Phi_mulVec]
    simp only [hv, zero_smul, Finset.sum_const_zero, add_zero, mulVec_sum, mulVec_smul]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
    exact spanLt_mono e (Fin.is_le c) (hmem c)

end Main

end Formalism.L2.SG.RealObj.ThreeBlockFrameInverses
