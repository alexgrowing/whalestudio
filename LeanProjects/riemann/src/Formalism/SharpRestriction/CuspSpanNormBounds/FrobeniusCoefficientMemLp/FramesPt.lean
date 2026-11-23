import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BigCellConjI
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

def tB (r : ℕ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | o, (t, s) :: bs => ((-1 : ℂ) ^ r * (-Complex.I) ^ (2 * o + s - 1) * t, s) :: tB r (o + s) bs

theorem ptEntry_tB (r : ℕ) : ∀ (bs : List (ℂ × ℕ)) (o i j : ℕ),
    ptEntry (tB r o bs) i j = (-1 : ℂ) ^ r * (-Complex.I) ^ (2 * o + i + j) * ptEntry bs i j
  | [], o, i, j => by simp [tB, ptEntry]
  | (t, s) :: bs, o, i, j => by
    simp only [tB, ptEntry]
    split_ifs with h1 h2 h3
    · have e : 2 * o + s - 1 = 2 * o + i + j := by omega
      rw [e]
    · ring
    · rw [ptEntry_tB r bs (o + s) (i - s) (j - s)]
      have e : 2 * (o + s) + (i - s) + (j - s) = 2 * o + i + j := by omega
      rw [e]
    · ring

theorem tB_snd (r : ℕ) : ∀ (bs : List (ℂ × ℕ)) (o : ℕ), (tB r o bs).map Prod.snd = bs.map Prod.snd
  | [], _ => rfl
  | (t, s) :: bs, o => by simp [tB, tB_snd r bs (o + s)]

theorem unit_ne (r e : ℕ) : (-1 : ℂ) ^ r * (-Complex.I) ^ e ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero))

theorem unit_normSq (r e : ℕ) : Complex.normSq ((-1 : ℂ) ^ r * (-Complex.I) ^ e) = 1 := by
  simp [map_mul, map_pow]

theorem tB_mem (r : ℕ) : ∀ (bs : List (ℂ × ℕ)) (o : ℕ), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ b ∈ tB r o bs, b.1 ≠ 0 ∧ 1 ≤ b.2
  | [], _, _ => by simp [tB]
  | (t, s) :: bs, o, h => by
    intro b hb
    simp only [tB, List.mem_cons] at hb
    rcases hb with rfl | hb
    · have h0 := h (t, s) (by simp)
      exact ⟨mul_ne_zero (unit_ne r _) h0.1, h0.2⟩
    · exact tB_mem r bs (o + s) (fun b hb => h b (by simp [hb])) b hb

def turnPt {r : ℕ} (p : Point ℂ (r + 1)) : Point ℂ (r + 1) :=
  ⟨tB r 0 p.1, tB_mem r p.1 0 p.2.1, by rw [tB_snd]; exact p.2.2⟩

theorem ptMat_turnPt {r : ℕ} (p : Point ℂ (r + 1)) (a b : Fin (r + 1)) :
    ptMat (turnPt p) a b = (-1 : ℂ) ^ r * (-Complex.I) ^ (a.val + b.val) * ptMat p a b := by
  show ptEntry (tB r 0 p.1) a.val b.val = _
  rw [ptEntry_tB]
  simp [ptMat]

theorem blockIdx_tB (r : ℕ) : ∀ (bs : List (ℂ × ℕ)) (o q : ℕ), blockIdx (tB r o bs) q = blockIdx bs q
  | [], _, _ => rfl
  | (t, s) :: bs, o, q => by
    simp only [tB, blockIdx]
    split_ifs
    · rfl
    · rw [blockIdx_tB r bs (o + s)]

theorem rootPat_turnPt {r : ℕ} (p : Point ℂ (r + 1)) : rootPat (turnPt p) = rootPat p := by
  unfold rootPat
  simp only [turnPt, blockIdx_tB]

theorem ptWeightFrom_tB (k r : ℕ) (T T' : ℝ) : ∀ (bs : List (ℂ × ℕ)) (o a : ℕ),
    ptWeightFrom k r T T' a (tB r o bs) = ptWeightFrom k r T T' a bs
  | [], _, _ => rfl
  | (t, s) :: bs, o, a => by
    simp only [tB, ptWeightFrom]
    rw [ptWeightFrom_tB k r T T' bs (o + s) (a + s)]
    congr 1
    have h1 : Complex.normSq ((-1 : ℂ) ^ r * (-Complex.I) ^ (2 * o + s - 1) * t) = Complex.normSq t := by
      rw [map_mul, unit_normSq, one_mul]
    have h2 : ‖(-1 : ℂ) ^ r * (-Complex.I) ^ (2 * o + s - 1) * t‖ = ‖t‖ := by
      rw [norm_mul]
      have : ‖(-1 : ℂ) ^ r * (-Complex.I) ^ (2 * o + s - 1)‖ = 1 := by simp
      rw [this, one_mul]
    rw [h1, h2]

theorem ptWeight_turnPt (k r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)) : ptWeight k r T T' (turnPt p) = ptWeight k r T T' p :=
  ptWeightFrom_tB k r T T' p.1 0 0

theorem leadMinor_turnPt {r : ℕ} (p : Point ℂ (r + 1)) (l : ℕ) (hl : l ≤ r + 1) :
    Complex.normSq (leadMinor (ptMat (turnPt p)) l hl) = Complex.normSq (leadMinor (ptMat p) l hl) := by
  unfold leadMinor
  set e := Fin.castLE hl
  have hM : (ptMat (turnPt p)).submatrix e e =
      Matrix.diagonal (fun a => (-1 : ℂ) ^ r * (-Complex.I) ^ (e a).val) * (ptMat p).submatrix e e *
        Matrix.diagonal (fun b => (-Complex.I) ^ (e b).val) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, ptMat_turnPt, pow_add]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul, map_prod,
    map_prod]
  have h1 : ∀ a : Fin l, Complex.normSq ((-1 : ℂ) ^ r * (-Complex.I) ^ (e a).val) = 1 := fun a => unit_normSq _ _
  have h2 : ∀ b : Fin l, Complex.normSq ((-Complex.I) ^ (e b).val) = 1 := fun b => by simp [map_pow]
  simp only [h1, h2, Finset.prod_const_one, one_mul, mul_one]

theorem GPoint_turnPt {r : ℕ} (T T' : ℝ) (p : Point ℂ (r + 1)) : Gpt T T' (turnPt p) = Gpt T T' p := by
  unfold Gpt
  rw [leadMinor_turnPt, leadMinor_turnPt]

theorem tT_mulVec_bvec {k r : ℕ} (i : Fin (2 * r + k + 1)) : tT k r *ᵥ bvec i = dT k r i • bvec i := by
  funext j
  unfold tT bvec
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [h]
  · ring

theorem tT_mulVec_fvec {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    tT k r *ᵥ fvec k r z a = Complex.I ^ a.val • fvec k r z a := by
  unfold fvec
  split_ifs with h
  · rw [tT_mulVec_bvec, dT_eI]
  · rw [tT_mulVec_Wb hz]
    have : a.val = r := by have := a.isLt; omega
    rw [this]

theorem Hpk_tTi {k r : ℕ} : Hpk k r * tTi k r = (tT k r)ᴴ * Hpk k r := by
  have h : (tT k r)ᴴ * Hpk k r * tT k r = Hpk k r := tT_mem_UH k r
  calc Hpk k r * tTi k r = (tT k r)ᴴ * Hpk k r * tT k r * tTi k r := by rw [h]
    _ = (tT k r)ᴴ * Hpk k r := by rw [Matrix.mul_assoc _ (tT k r), tT_mul_tTi, Matrix.mul_one]

theorem herm_tTi {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (tTi k r *ᵥ v) w = herm (Hpk k r) v (tT k r *ᵥ w) := by
  unfold herm
  rw [Matrix.mulVec_mulVec, Hpk_tTi, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem herm_smul_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v w : Fin m → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_smul_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v w : Fin m → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem Zhat_conjI {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (g : Mx k r) (a b : Fin (r + 1)) :
    Zhat k r z z' (tTi k r * g * tT k r) a b = Complex.I ^ b.val * star (Complex.I ^ a.val) * Zhat k r z z' g a b := by
  unfold Zhat
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_tTi, tT_mulVec_fvec hz', tT_mulVec_fvec hz,
    Matrix.mulVec_smul, herm_smul_left, herm_smul_right]
  ring

theorem phase_id (r a b : ℕ) (hb : b ≤ r) :
    Complex.I ^ b * star (Complex.I ^ a) * (-1 : ℂ) ^ (r - b) = (-1 : ℂ) ^ r * (-Complex.I) ^ (a + b) := by
  have hs : star (Complex.I ^ a) = (-Complex.I) ^ a := by
    rw [star_pow, Complex.star_def, Complex.conj_I]
  have hI : Complex.I ^ b = (-1 : ℂ) ^ b * (-Complex.I) ^ b := by
    rw [← mul_pow]; congr 1; ring
  have hr : (-1 : ℂ) ^ r = (-1 : ℂ) ^ b * (-1 : ℂ) ^ (r - b) := by
    rw [← pow_add]; congr 1; omega
  rw [hs, hI, hr, pow_add]
  ring

theorem ZhatO_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a b : Fin (r + 1)) :
    Zhat k r z z' g a b = (-1 : ℂ) ^ (r - b.val) * ZhatO k r z z' g a b := by
  unfold ZhatO
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem Zhat_conjI_turn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g : Mx k r} {p : Point ℂ (r + 1)} (h : ZhatO k r z z' g = ptMat p) :
    Zhat k r z z' (tTi k r * g * tT k r) = ptMat (turnPt p) := by
  ext a b
  rw [Zhat_conjI hz hz', ZhatO_eq, h, ptMat_turnPt, ← phase_id r a.val b.val (by have := b.isLt; omega)]
  ring

end Formalism.MainNotions.S.Pv.Frames

end
