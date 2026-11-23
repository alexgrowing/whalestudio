import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeDec

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sd_eq (A : Gn g (m + 1)) :
    superDiag A = ∑ l : Fin m, (A : Mt g (m + 1)) (Fin.castSucc l) (Fin.succ l) := by
  unfold superDiag
  simp_rw [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_eq_zero (fun k _ => if_neg (by have := k.2; simp only [Fin.val_last]; omega)), add_zero]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_eq_single (Fin.succ l)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by simp [h]))
  · simp

theorem trace_phi (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    trace ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) - ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) 0 0 =
      superDiag (umGL p.1) := by
  rw [phi_val]
  simp only [Matrix.trace, Matrix.diag, cyc_mul_apply]
  rw [← Equiv.sum_comp (finRotate (m + 1))]
  simp only [Equiv.symm_apply_apply]
  rw [Fin.sum_univ_castSucc, finRotate_last, rot_symm_zero, add_sub_cancel_right, sd_eq, umGL_val]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [rot_castSucc, hp_um_row _ _ _ (Fin.castSucc_lt_last l).ne]

theorem isRowFix_conj {j : ℕ} (r : Fin (m + 1) → ZMod g) (hr : ∀ l : Fin (m + 1), (l : ℕ) ≤ j → r l = 0)
    (hr0 : r (Fin.last m) ≠ 0) : IsRowFix j (cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹) := by
  have he : ∀ i k, ((cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) i k =
      Hp r ((finRotate (m + 1)).symm i) ((finRotate (m + 1)).symm k) := fun i k => by
    rw [Units.val_mul, Units.val_mul, mul_cycinv_apply, cyc_mul_apply, hpGL_val]
  refine ⟨fun i k hi => ?_, fun i k hi hk0 hk => ?_⟩
  · have hi' : i ≠ 0 := fun h => hi (by simp [h])
    rw [he]
    simp only [Hp, Matrix.of_apply, if_neg (rot_symm_ne_last i hi'), Matrix.one_apply,
      (finRotate (m + 1)).symm.apply_eq_iff_eq]
  · have hi' : i = 0 := Fin.ext hi
    have hk' : k ≠ 0 := fun h => by simp [h] at hk0
    subst hi'
    rw [he, rot_symm_zero]
    simp only [Hp, Matrix.of_apply, if_pos rfl]
    have hv := rot_symm_val k hk'
    exact hr _ (by omega)

theorem phi_inj {j : ℕ} {p q : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)} (h : phi j p = phi j q) :
    p = q := by
  obtain ⟨N1, t1, w1⟩ := p
  obtain ⟨N2, t2, w2⟩ := q
  unfold phi at h
  rw [mul_assoc, mul_assoc] at h
  have h1 := mul_left_cancel h
  have hz := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1))) h1
  simp only [Units.val_mul, hpGL_val, umGL_val] at hz
  have hN : N1 = N2 := by
    funext q
    have hne : q.1.1 ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le q.2 (Fin.le_last _))
    have := congrFun (congrFun hz q.1.1) q.1.2
    rw [hp_um_row _ _ _ hne, hp_um_row _ _ _ hne] at this
    simpa [Um, ne_of_lt q.2, q.2] using this
  subst hN
  have h2 := mul_right_cancel h1
  have hr : ∀ k, rvec j t1 w1 k = rvec j t2 w2 k := fun k => by
    have := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1)) (Fin.last m) k) h2
    simpa [hpGL_val, Hp] using this
  have ht : t1 = t2 := Units.ext (by simpa [rvec_last] using hr (Fin.last m))
  have hw : w1 = w2 := by
    funext q
    have hq : q.1 ≠ Fin.last m := fun e => by
      have := q.2.2
      rw [e, Fin.val_last] at this
      omega
    simpa [rvec, hq, q.2] using hr q.1
  rw [ht, hw]

end DiscreteGroups.sglob.DzFe
