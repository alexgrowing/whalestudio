import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.MainNotions.S.Pv.Frames

variable {k r : ℕ}

private lemma apply_eq_ite_of_mulVec_bvec_eq' {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (hj : h *ᵥ bvec j = bvec j) (i : Fin n) : h i j = if i = j then 1 else 0 := by
  have e := congrFun hj i
  simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using e

private lemma Hpk_apply_sig_ne_zero {n : ℕ} {h H : Matrix (Fin n) (Fin n) ℂ} (hU : hᴴ * H * h = H) {p q : Fin n}
    (hcol : ∀ l, h l p = if l = p then 1 else 0) (hrow : ∀ m, H p m = if m = q then 1 else 0)
    (j : Fin n) : h q j = if q = j then 1 else 0 := by
  have hcolS : ∀ l, star (h l p) = if l = p then 1 else 0 := by
    intro l; rw [hcol]; split_ifs <;> simp
  have e1 : ∀ m, (hᴴ * H) p m = H p m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcolS, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e : (hᴴ * H * h) p j = H p j := by rw [hU]
  rw [Matrix.mul_apply] at e
  simp only [e1, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  rw [e]
  by_cases hq : q = j
  · subst hq; simp
  · simp [hq, Ne.symm hq]

private lemma Hpk_esI_apply_eq_ite_eI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) m = if m = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma Hpk_eI_apply_eq_ite_esI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) m = if m = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem fix_gen (d : Fin (2 * r + k + 1) → ℂ) (d0 : ℂ) (hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = d0)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : h ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, h *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ h *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : d i = d j := by
  have hUe : hᴴ * Hpk k r * h = Hpk k r := hU
  have colE : ∀ a : Fin r, ∀ l, h l (eI k r a) = if l = eI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).1
  have colS : ∀ a : Fin r, ∀ l, h l (esI k r a) = if l = esI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).2
  have rowE : ∀ a : Fin r, ∀ q, h (eI k r a) q = if eI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colS a) (Hpk_esI_apply_eq_ite_eI a)
  have rowS : ∀ a : Fin r, ∀ q, h (esI k r a) q = if esI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colE a) (Hpk_eI_apply_eq_ite_esI a)
  have out : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) →
      (∀ q, h p q = if p = q then 1 else 0) ∧ (∀ l, h l p = if l = p then 1 else 0) := by
    intro p hp
    rcases hp with hp | hp
    · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
      rw [← e]
      exact ⟨rowE _, colE _⟩
    · have hp2 := p.isLt
      have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p :=
        Fin.ext (show 2 * r + k - (2 * r + k - p.val) = p.val by omega)
      rw [← e]
      exact ⟨rowS _, colS _⟩
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [(out i hi).1 j] at hne
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (if_neg hij) hne
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [(out j hj).2 i] at hne
      by_cases hij : i = j
      · rw [hij]
      · exact absurd (if_neg hij) hne
    · push_neg at hi hj
      rw [hmid i hi.1 hi.2, hmid j hj.1 hj.2]

def dD (k r : ℕ) (δ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((δ ^ (r - i.val) : ℝ) : ℂ)
  else if r + k < i.val then (((δ ^ (r - (2 * r + k - i.val)))⁻¹ : ℝ) : ℂ) else 1

def tD (k r : ℕ) (δ : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.diagonal (dD k r δ)
def tDi (k r : ℕ) (δ : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal fun i => (dD k r δ i)⁻¹

variable {δ : ℝ}

end Formalism.L2.SG.Pf.Carrier.CarPinTor
