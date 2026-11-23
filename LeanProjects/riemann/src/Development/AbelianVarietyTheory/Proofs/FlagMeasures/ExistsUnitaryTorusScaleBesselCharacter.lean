import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TorusScale

variable {k r : ℕ}

def dS (k r : ℕ) (l : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then l ^ (r - i.val)
  else if r + k < i.val then (star (l ^ (r - (2 * r + k - i.val))))⁻¹ else 1

theorem dS_ne {l : ℂ} (hl : l ≠ 0) (i : Fin (2 * r + k + 1)) : dS k r l i ≠ 0 := by
  unfold dS
  split_ifs
  · exact pow_ne_zero _ hl
  · exact inv_ne_zero (star_ne_zero.2 (pow_ne_zero _ hl))
  · exact one_ne_zero

theorem dS_eI (l : ℂ) (a : Fin r) : dS k r l (eI k r a) = l ^ (r - a.val) := by
  unfold dS eI; simp [a.isLt]

theorem dS_mid (l : ℂ) (i : Fin (2 * r + k + 1)) (h : ¬ (i.val < r ∨ r + k < i.val)) : dS k r l i = 1 := by
  unfold dS
  rw [if_neg (by omega), if_neg (by omega)]

theorem dS_pair {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) :
    star (dS k r l i) * dS k r l j = 1 := by
  unfold dS
  rw [if_pos hi, if_neg (by omega), if_pos (by omega)]
  have : 2 * r + k - j.val = i.val := by omega
  rw [this]
  exact mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hl))

theorem diag_inv {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

theorem conj_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) (M : Matrix n n ℂ) (i j : n) :
    (diagonal d * M * (diagonal d)⁻¹) i j = d i * M i j * (d j)⁻¹ := by
  rw [diag_inv d hd]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diag_mem_UH (d : Fin (2 * r + k + 1) → ℂ) (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) :
    diagonal d ∈ UH (Hpk k r) := by
  show (diagonal d)ᴴ * Hpk k r * diagonal d = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hM : Hpk k r i j = 0
  · rw [hM]; ring
  · have := h i j hM
    rw [Pi.star_apply, mul_right_comm, this, one_mul]

theorem dS_Hpk {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    star (dS k r l i) * dS k r l j = 1 := by
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact dS_pair hl i j h1.1 h1.2
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have := congrArg star (dS_pair hl j i h2.1 (by omega))
    rw [star_mul, star_star, star_one] at this
    exact this
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [← h3.2.2, dS_mid l i (by omega)]; simp
  exfalso
  unfold Hpk at h
  rw [if_neg h1, if_neg h2, if_neg h3] at h
  exact h rfl

theorem conj_mem_N (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · refine Pv.Frames.UH_mul (Pv.Frames.UH_mul (diag_mem_UH d h) h1) ?_
    rw [diag_inv d hd]
    refine diag_mem_UH _ fun i j hij => ?_
    rw [star_inv₀, ← mul_inv, h i j hij, inv_one]
  · rw [conj_diag d hd, h2 a i hi]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring
  · rw [conj_diag d hd, h3 i j a b c]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring

theorem conj_mem_N_iff (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    n ∈ Nset k r ↔ diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  refine ⟨conj_mem_N d hd h, fun hn => ?_⟩
  have hd' : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
  have := conj_mem_N (fun i => (d i)⁻¹) hd'
    (fun i j hij => by rw [star_inv₀, ← mul_inv, h i j hij, inv_one]) hn
  convert this using 1
  ext i j
  rw [conj_diag _ hd', conj_diag _ hd]
  have := hd i
  have := hd j
  field_simp

theorem UW_col {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    h i j = if i = j then 1 else 0 := by
  have key : h *ᵥ bvec j = bvec j := by
    rcases hj with hj | hj
    · exact (hh.2.1 ⟨j.val, hj⟩).1
    · have := (hh.2.1 ⟨2 * r + k - j.val, by omega⟩).2
      have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
        apply Fin.ext
        have := j.isLt
        show 2 * r + k - (2 * r + k - j.val) = j.val
        omega
      rwa [e] at this
  have := congrFun key i
  simpa [bvec, Pi.single_apply] using this

theorem Hpk_outer (i j p : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) (hij : i.val + j.val = 2 * r + k) :
    Hpk k r j p = if p = i then 1 else 0 := by
  unfold Hpk
  by_cases e : p = i
  · subst e
    rw [if_pos rfl]
    by_cases h1 : j.val < r
    · rw [if_pos ⟨h1, by omega⟩]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e' : p.val ≠ i.val := fun x => e (Fin.ext x)
    rw [if_neg e, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem UW_row {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    h i j = if j = i then 1 else 0 := by
  have hi0 := i.isLt
  let q : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hq : q.val < r ∨ r + k < q.val := by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega
  have hiq : i.val + q.val = 2 * r + k := by show i.val + (2 * r + k - i.val) = _; omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have := congrFun (congrFun hU q) j
  rw [Hpk_outer i q j hq hiq, Matrix.mul_assoc, Matrix.mul_apply] at this
  simp only [Matrix.conjTranspose_apply, UW_col hh _ q hq] at this
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp), Matrix.mul_apply] at this
  simp only [Hpk_outer i q _ hq hiq] at this
  simpa using this

theorem dS_comm (l : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : diagonal (dS k r l) * h = h * diagonal (dS k r l) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [UW_col hh i j hj]
    split_ifs with e
    · rw [e]; ring
    · ring
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [UW_row hh i j hi]
    split_ifs with e
    · rw [e]; ring
    · ring
  rw [dS_mid l i hi, dS_mid l j hj]; ring

theorem diag_fix (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → d i = 1)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : diagonal d *ᵥ z = z := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h]; ring
  · rw [hd i h, one_mul]

theorem inv_fix {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (diagonal (dS k r l))⁻¹ *ᵥ z = z := by
  rw [diag_inv _ (dS_ne hl)]
  exact diag_fix _ (fun i hi => by rw [dS_mid l i hi, inv_one]) hz

theorem ell_conj {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (diagonal (dS k r l) * M * (diagonal (dS k r l))⁻¹) = l * ell k r z M := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [conj_diag _ (dS_ne hl), dS_eI, dS_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have := pow_ne_zero (r - (a.val + 1)) hl
    field_simp
  · have hra : r - a.val = 1 := by have := a.isLt; omega
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hl hz, Matrix.mulVec_diagonal, dS_eI, hra, pow_one]

theorem pow_bound {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : m ≤ r) :
    (x / 2) ^ m ≤ max (x / 2) (2 / x) ^ r ∧ (2 / x) ^ m ≤ max (x / 2) (2 / x) ^ r := by
  have h1 : 1 ≤ max (x / 2) (2 / x) := by
    rcases le_total x 2 with h | h
    · exact le_max_of_le_right ((one_le_div hx).2 h)
    · exact le_max_of_le_left ((one_le_div two_pos).2 h)
  exact ⟨(pow_le_pow_left₀ (by positivity) (le_max_left _ _) m).trans (pow_le_pow_right₀ h1 hm),
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m).trans (pow_le_pow_right₀ h1 hm)⟩

theorem exists_torus_scale : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  intro k r c hc
  have hS : cStd ≠ 0 := by unfold cStd; simp
  have hl : cStd / c ≠ 0 := div_ne_zero hS hc
  have hn : ‖cStd / c‖ = 2 / ‖c‖ := by unfold cStd; simp
  have hx : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨diagonal (dS k r (cStd / c)), diag_mem_UH _ (dS_Hpk hl), conj_mem_N_iff _ (dS_ne hl) (dS_Hpk hl),
    fun z hz => ⟨diag_fix _ (dS_mid _) hz, fun h hh => dS_comm _ hh, fun n _ => ?_⟩, fun a => ?_⟩
  · unfold psi
    rw [ell_conj hl hz, ← mul_assoc, mul_div_cancel₀ _ hc]
  · have hb := pow_bound (r := r) hx (Nat.sub_le r a.val)
    refine ⟨((cStd / c) ^ (r - a.val))⁻¹, inv_ne_zero (pow_ne_zero _ hl), ?_, ?_, fun z hz => ?_⟩
    · rw [norm_inv, norm_pow, hn, ← inv_pow, inv_div]; exact hb.1
    · rw [norm_inv, inv_inv, norm_pow, hn]; exact hb.2
    · unfold fvec
      split_ifs with h
      · rw [diag_inv _ (dS_ne hl)]
        funext i
        rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases e : i = eI k r ⟨a.val, h⟩
        · rw [e, dS_eI]
        · simp [bvec, e]
      · have : r - a.val = 0 := by omega
        rw [inv_fix hl hz, this]; simp

end GlobalTheory.TorusScale

end
