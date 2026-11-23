import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.Dilation

variable {k r : ℕ}

def dd (k r : ℕ) (τ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then ((r - i.val : ℕ) : ℤ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℤ)

theorem dil_eq (τ : ℝ) : dil k r τ = Matrix.diagonal (dd k r τ) := rfl

theorem dd_eq_zpow {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i = (τ : ℂ) ^ wt k r i := by
  unfold dd wt
  split_ifs
  · rw [_root_.zpow_natCast]
  · rw [_root_.zpow_zero]
  · rw [_root_.zpow_neg, _root_.zpow_natCast]

theorem dd_inv_mul {τ : ℝ} (hτ : τ ≠ 0) (i j : Fin (2 * r + k + 1)) :
    dd k r τ⁻¹ i * dd k r τ j = (τ : ℂ) ^ (wt k r j - wt k r i) := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow (inv_ne_zero hτ), dd_eq_zpow hτ, Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    neg_add_eq_sub]

theorem dd_mul_inv {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i * dd k r τ⁻¹ i = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow hτ, dd_eq_zpow (inv_ne_zero hτ), Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    add_neg_cancel, _root_.zpow_zero]

theorem star_dd (τ : ℝ) (i : Fin (2 * r + k + 1)) : star (dd k r τ i) = dd k r τ i := by
  unfold dd
  split_ifs <;> simp

theorem dd_pair {τ : ℝ} (hτ : τ ≠ 0) {i j : Fin (2 * r + k + 1)} (h : i.val < r ∨ j.val < r)
    (hs : i.val + j.val = 2 * r + k) : dd k r τ i * dd k r τ j = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have hw : wt k r i + wt k r j = 0 := by
    have := i.isLt
    have := j.isLt
    unfold wt
    split_ifs <;> omega
  rw [dd_eq_zpow hτ, dd_eq_zpow hτ, ← _root_.zpow_add₀ h0, hw, _root_.zpow_zero]

theorem dd_middle (τ : ℝ) {i : Fin (2 * r + k + 1)} (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    dd k r τ i = 1 := by
  unfold dd
  rw [if_neg (by omega), if_pos h2]

theorem dil_entry (a b : ℝ) (m : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (dil k r a * m * dil k r b) i j = dd k r a i * m i j * dd k r b j := by
  rw [dil_eq, dil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dil_mul_inv {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ * dil k r τ⁻¹ = 1 := by
  rw [dil_eq, dil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dd_mul_inv hτ i

theorem dil_inv {τ : ℝ} (hτ : τ ≠ 0) : (dil k r τ)⁻¹ = dil k r τ⁻¹ := by
  exact Matrix.inv_eq_right_inv (dil_mul_inv hτ)

theorem uh_mul {g h : Mat k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem dil_mem {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ ∈ UH (Hpk k r) := by
  show (dil k r τ)ᴴ * Hpk k r * dil k r τ = Hpk k r
  ext i j
  rw [dil_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, star_dd]
  by_cases h1 : (i.val < r ∨ j.val < r) ∧ i.val + j.val = 2 * r + k
  · rw [mul_right_comm, dd_pair hτ h1.1 h1.2, one_mul]
  · by_cases h2 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
    · obtain ⟨hr, hk, rfl⟩ := h2
      rw [dd_middle τ hr hk, one_mul, mul_one]
    · have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (fun hc => h1 ⟨Or.inl hc.1, hc.2⟩), if_neg (fun hc => h1 ⟨Or.inr hc.1, hc.2⟩),
          if_neg h2]
      rw [h0, mul_zero, zero_mul]

theorem Hpk_row {i p t : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val)
    (hs : i.val + p.val = 2 * r + k) : Hpk k r p t = if t = i then 1 else 0 := by
  have hpo : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
  simp only [Hpk]
  rcases eq_or_ne t i with rfl | hti
  · rw [if_pos rfl]
    rcases h with h | h
    · rw [if_neg (by omega), if_pos ⟨h, by omega⟩]
    · rw [if_pos ⟨by omega, by omega⟩]
  · have hv : t.val ≠ i.val := fun e => hti (Fin.ext e)
    rw [if_neg hti, if_neg (by omega), if_neg (by omega), if_neg (fun hc => hpo ⟨hc.1, hc.2.1⟩)]

theorem uw_col {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1)} (hp : p.val < r ∨ r + k < p.val) (s : Fin (2 * r + k + 1)) :
    h s p = if s = p then 1 else 0 := by
  have hcol : ∀ q : Fin (2 * r + k + 1), h *ᵥ bvec q = bvec q → h s q = if s = q then 1 else 0 := by
    intro q hq
    have e := congrFun hq s
    simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using e
  have hpl := p.isLt
  rcases hp with hp | hp
  · have hq : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have := (hh.2.1 ⟨p.val, hp⟩).1
    rw [hq] at this
    exact hcol p this
  · have hq : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have := (hh.2.1 ⟨2 * r + k - p.val, by omega⟩).2
    rw [hq] at this
    exact hcol p this

theorem uw_zero {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    h i j = 0 := by
  have hil := i.isLt
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  let p : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hpv : p.val = 2 * r + k - i.val := rfl
  have hpo : p.val < r ∨ r + k < p.val := by omega
  have hip : i.val + p.val = 2 * r + k := by omega
  have hcol := uw_col hh hpo
  have hrow : ∀ t, Hpk k r p t = if t = i then 1 else 0 := fun t => Hpk_row hi hip
  have hleft : ∀ t, (hᴴ * Hpk k r) p t = Hpk k r p t := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [Matrix.conjTranspose_apply, hcol]
    · intro s _ hs
      simp [Matrix.conjTranspose_apply, hcol, hs]
    · simp
  have e := congrFun (congrFun hU p) j
  rw [Matrix.mul_apply] at e
  simp only [hleft, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  have hji : j ≠ i := fun hc => by subst hc; omega
  rw [if_neg hji] at e
  exact e

theorem dil_comm {z : Fin (2 * r + k + 1) → ℂ} (τ : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    dil k r τ * h = h * dil k r τ := by
  ext i j
  rw [dil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [uw_col hh hj i]
    split_ifs with e
    · subst e
      rw [one_mul, mul_one]
    · rw [mul_zero, zero_mul]
  · have hj' : r ≤ j.val ∧ j.val ≤ r + k := by omega
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_zero hh hi hj'.1 hj'.2, mul_zero, zero_mul]
    · rw [dd_middle τ (by omega) (by omega), dd_middle τ hj'.1 hj'.2, one_mul, mul_one]

private theorem conj_mem_lemma {τ : ℝ} (hτ : τ ≠ 0) (m : Mat k r) (i j : Fin (2 * r + k + 1))
    (h : m i j = if i = j then 1 else 0) :
    (dil k r τ * m * dil k r τ⁻¹) i j = if i = j then 1 else 0 := by
  rw [dil_entry, h]
  split_ifs with e
  · subst e
    rw [mul_one, dd_mul_inv hτ]
  · rw [mul_zero, zero_mul]

theorem conj_mem {τ : ℝ} (hτ : τ ≠ 0) {m : Mat k r} (hm : m ∈ Nset k r) :
    dil k r τ * m * dil k r τ⁻¹ ∈ Nset k r := by
  have hU : m ∈ UH (Hpk k r) := hm.1
  have hc : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      m i (eI k r a) = if i = eI k r a then 1 else 0 := hm.2.1
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  refine ⟨uh_mul (uh_mul (dil_mem hτ) hU) (dil_mem (inv_ne_zero hτ)), ?_, ?_⟩
  · intro a i hai
    exact conj_mem_lemma hτ m i _ (hc a i hai)
  · intro i j h1 h2 h3
    exact conj_mem_lemma hτ m i j (hb i j h1 h2 h3)

theorem wt_lt {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hn : ¬ (r ≤ i.val ∧ j.val ≤ r + k)) :
    wt k r j + 1 ≤ wt k r i := by
  unfold wt
  split_ifs <;> omega

private theorem apply_self_eq_one_of_mem_Nset {m : Mat k r} (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1)) :
    m i i = if i = i then 1 else 0 :=
  Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i i le_rfl

theorem contract {τ : ℝ} (hτ : 1 ≤ τ) {m : Mat k r} (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) :
    ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖ := by
  have hpos : 0 < τ := by linarith
  have hτ0 : τ ≠ 0 := hpos.ne'
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  rw [dil_inv hτ0, Matrix.sub_apply, Matrix.sub_apply, dil_entry, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hij' : i.val < j.val := hij
    rw [if_neg hij.ne, sub_zero, sub_zero]
    by_cases hmid : r ≤ i.val ∧ j.val ≤ r + k
    · have h0 : m i j = 0 := by
        have e := hb i j (by omega) hmid.2 hmid.1
        rwa [if_neg hij.ne] at e
      rw [h0]
      simp
    · have hw := wt_lt (k := k) (r := r) hij' hmid
      rw [mul_right_comm, dd_inv_mul hτ0, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← _root_.zpow_neg_one]
      exact _root_.zpow_le_zpow_right₀ hτ (by omega)
  · have h1 : m i i = 1 := by simpa using apply_self_eq_one_of_mem_Nset hm i
    rw [h1, if_pos rfl, mul_one, dd_inv_mul hτ0, sub_self, _root_.zpow_zero]
    simp
  · have h0 : m i j = 0 := by
      have e := Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i j hij.le
      rwa [if_neg hij.ne'] at e
    rw [if_neg hij.ne', h0]
    simp

theorem main : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  intro k r z _
  refine ⟨fun τ hτ => ⟨dil_mem hτ.ne', fun h hh => dil_comm τ hh, fun m hm => ⟨?_, ?_⟩⟩,
    fun τ hτ m hm i j => contract hτ hm i j⟩
  · rw [dil_inv hτ.ne']
    exact conj_mem hτ.ne' hm
  · have e := conj_mem (inv_ne_zero hτ.ne') hm
    rwa [inv_inv, ← dil_inv hτ.ne'] at e

end GlobalTheory.SgInf.Dilation
