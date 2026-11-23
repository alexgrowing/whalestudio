import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Psi

variable {k r : ℕ}

def ellT (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (eI k r a) (eI k r ⟨a.val + 1, h⟩) else (g *ᵥ z) (eI k r a)

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : ell k r z g = ∑ a, ellT k r z g a := rfl

theorem uw_coordX {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z)
    (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) : (h *ᵥ y) (eI k r b) = y (eI k r b) := by
  rw [← herm_esI (h *ᵥ y) b, ← (hh.2.1 b).2, herm_inv hh.1, herm_esI]

theorem ellT_conj {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (g : Mx k r) (a : Fin r) :
    ellT k r z (h⁻¹ * g * h) a = ellT k r z g a := by
  have hh' := uw_inv hh
  have hrow : ∀ l, h⁻¹ (eI k r a) l = if eI k r a = l then 1 else 0 := fun l => by
    have h1 := uw_coordX hh' (bvec l) a
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using h1
  unfold ellT
  split_ifs with hlt
  · have hcol : ∀ l, h l (eI k r ⟨a.val + 1, hlt⟩) = if l = eI k r ⟨a.val + 1, hlt⟩ then 1 else 0 := by
      intro l
      have h1 := congrFun (hh.2.1 ⟨a.val + 1, hlt⟩).1 l
      simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using h1
    simp [Matrix.mul_apply, hcol, hrow]
  · rw [← Matrix.mulVec_mulVec, hh.2.2, ← Matrix.mulVec_mulVec, uw_coordX hh' _ a]

theorem ell_conj {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (g : Mx k r) :
    ell k r z (h⁻¹ * g * h) = ell k r z g := by
  rw [ell_eq, ell_eq]
  exact Finset.sum_congr rfl fun a _ => ellT_conj hh g a

theorem n_last {n : Mx k r} (hn : n ∈ Nset k r) {d : Fin (2 * r + k + 1) → ℂ} (hd : d ∈ lowS k r r)
    (a : Fin r) (ha : ¬ a.val + 1 < r) : (n *ᵥ d) (eI k r a) = d (eI k r a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · rw [hn.2.1 a (eI k r a) le_rfl, if_pos rfl, one_mul]
  · intro j _ hj
    by_cases hjr : r ≤ j.val
    · rw [hd j hjr, mul_zero]
    · push_neg at hjr
      have h1 := hn.2.1 ⟨j.val, hjr⟩ (eI k r a) (by simp only [eI]; omega)
      rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl, if_neg (Ne.symm hj)] at h1
      rw [h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ellT_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n m : Mx k r} (hn : n ∈ Nset k r)
    (hm : m ∈ Nset k r) (a : Fin r) : ellT k r z (n * m) a = ellT k r z n a + ellT k r z m a := by
  unfold ellT
  split_ifs with hlt
  · rw [Matrix.mul_apply]
    have hab : eI k r a ≠ eI k r ⟨a.val + 1, hlt⟩ := by
      intro h
      have h1 := congrArg Fin.val h
      simp [eI] at h1
    rw [Finset.sum_eq_add (eI k r a) (eI k r ⟨a.val + 1, hlt⟩) hab]
    · rw [hn.2.1 a (eI k r a) le_rfl, if_pos rfl, one_mul,
        hm.2.1 ⟨a.val + 1, hlt⟩ (eI k r ⟨a.val + 1, hlt⟩) le_rfl, if_pos rfl, mul_one, add_comm]
    · intro c _ hc
      by_cases hcb : a.val + 1 ≤ c.val
      · rw [hm.2.1 ⟨a.val + 1, hlt⟩ c hcb, if_neg hc.2, mul_zero]
      · push_neg at hcb
        have hcr : c.val < r := by omega
        have h1 := hn.2.1 ⟨c.val, hcr⟩ (eI k r a) (by simp only [eI]; omega)
        rw [show eI k r ⟨c.val, hcr⟩ = c from Fin.ext rfl, if_neg (Ne.symm hc.1)] at h1
        rw [h1, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hd := n_on_Wb hm hz
    have hz0 : z (eI k r a) = 0 := hz _ (Or.inl (by simp [eI]))
    have key : n *ᵥ (m *ᵥ z) = n *ᵥ z + n *ᵥ (m *ᵥ z - z) := by
      rw [← Matrix.mulVec_add]
      congr 1
      abel
    rw [← Matrix.mulVec_mulVec, key, Pi.add_apply, n_last hn hd a hlt, Pi.sub_apply, hz0, sub_zero]

theorem ell_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n m : Mx k r} (hn : n ∈ Nset k r)
    (hm : m ∈ Nset k r) : ell k r z (n * m) = ell k r z n + ell k r z m := by
  rw [ell_eq, ell_eq, ell_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => ellT_mul hz hn hm a

theorem ell_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : ell k r z 1 = 0 := by
  rw [ell_eq]
  apply Finset.sum_eq_zero
  intro a _
  unfold ellT
  split_ifs with hlt
  · rw [Matrix.one_apply, if_neg]
    intro h
    have h1 := congrArg Fin.val h
    simp [eI] at h1
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [eI]))

theorem psi_add (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {g g' g'' : Mx k r}
    (h : ell k r z g = ell k r z g' + ell k r z g'') :
    psi k r z c g = psi k r z c g' * psi k r z c g'' := by
  unfold psi
  rw [h, mul_add, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem psiAll : PsiAll := by
  intro k r z c hz
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h0 : ∀ g, ell k 0 z g = 0 := fun g => by simp [ell_eq]
    refine ⟨fun n _ m _ => ?_, fun h _ n _ => ?_, fun h _ n _ => ?_, fun n _ => ?_⟩ <;> simp [psi, h0]
  have hunitW : ∀ h ∈ UWset k r z, IsUnit h.det := fun h hh => by
    by_contra hdet
    have h0 : h⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit h hdet
    have h1 := congrFun ((uw_inv hh).2.1 ⟨0, hr⟩).1 (eI k r ⟨0, hr⟩)
    rw [h0, Matrix.zero_mulVec] at h1
    simp [bvec] at h1
  have hunitN : ∀ n ∈ Nset k r, IsUnit n.det := fun n hn => by
    by_contra hdet
    have h0 : n⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit n hdet
    have h1 := (n_inv hn).2.1 ⟨0, hr⟩ (eI k r ⟨0, hr⟩) le_rfl
    rw [h0, if_pos rfl] at h1
    simp at h1
  refine ⟨fun n hn m hm => psi_add z c (ell_mul hz hn hm), fun h hh n hn => ?_, fun h hh n hn => ?_,
    fun n hn => ?_⟩
  · unfold psi
    rw [ell_conj hh n]
  · have hh' := uw_inv hh
    have hinv : (h⁻¹)⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h (hunitW h hh)
    have h1 := ell_conj hh' n
    rw [hinv] at h1
    unfold psi
    rw [h1]
  · have h1 : ell k r z (n * n⁻¹) = ell k r z n + ell k r z n⁻¹ := ell_mul hz hn (n_inv hn)
    rw [Matrix.mul_nonsing_inv n (hunitN n hn), ell_one hz] at h1
    have h2 : ell k r z n⁻¹ = -ell k r z n := by linear_combination (-1 : ℂ) * h1
    unfold psi
    rw [h2, mul_neg, Complex.neg_re, Complex.ofReal_neg, mul_neg]
    show _ = (starRingEnd ℂ) _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]

end Psi

end PI.WBL.Cv
