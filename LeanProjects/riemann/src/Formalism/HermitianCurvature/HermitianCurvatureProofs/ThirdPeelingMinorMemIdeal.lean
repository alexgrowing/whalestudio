import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstPeelingMinorMemIdeal

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem pe_lt {k r p : ℕ} (h : p < 2 * r + k + 1) : (pe k r p).val = p := by
  rw [pe_val]
  omega

theorem herm_wsum (k r : ℕ) (v y : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    herm (Hpk k r) v y = ∑ w : Fin (k + 1), v (wI k r w) * herm (Hpk k r) (bvec (wI k r w)) y := by
  have hv' : v = ∑ w : Fin (k + 1), v (wI k r w) • bvec (wI k r w) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, smul_eq_mul]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [Finset.sum_eq_single ⟨i.val - r, by omega⟩]
      · have e : wI k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [wI]; omega)
        rw [e, Pi.single_eq_same, mul_one]
      · intro w _ hw
        rw [Pi.single_eq_of_ne, mul_zero]
        intro e
        apply hw
        apply Fin.ext
        have := congrArg Fin.val e
        simp only [wI, Fin.val_mk] at this ⊢
        omega
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro w _
      rw [Pi.single_eq_of_ne, mul_zero]
      intro e
      have := congrArg Fin.val e
      simp only [wI] at this
      omega
  conv_lhs => rw [hv']
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem dpsi_e_w (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ) (hp : p < r) (w : Fin (k + 1)) :
    dpsiP k r z' (pe k r p) (wI k r w) = if p + 1 = r then z' (wI k r w) else 0 := by
  have h1 : min p (2 * r + k) = p := by omega
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, pe_val, h1, hw]
  rw [if_neg (by omega), if_pos (by omega)]

theorem dpsi_middle_last_basis (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (l : ℕ) (hl : l < r) (w : Fin (k + 1)) :
    dpsiP k r z' (wI k r w) (ps k r l) = if l + 1 = r then herm (Hpk k r) (bvec (wI k r w)) z' else 0 := by
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, ps_val, hw]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp only [show (2 * r + k - l = r + k + 1) ↔ (l + 1 = r) by omega]

theorem dpsi_last_basis_shift (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (a b : ℕ) (ha : a < r) (hb : b < r) :
    dpsiP k r z' (ps k r a) (ps k r b) = if b + 1 = a then 1 else 0 := by
  have c1 : ¬(2 * r + k - a < r ∧ 2 * r + k - b < r) := by omega
  have c2 : ¬(2 * r + k - a < r ∧ r ≤ 2 * r + k - b ∧ 2 * r + k - b ≤ r + k) := by omega
  have c3 : ¬(r ≤ 2 * r + k - a ∧ 2 * r + k - a ≤ r + k ∧ r + k < 2 * r + k - b) := by omega
  have c4 : r + k < 2 * r + k - a ∧ r + k < 2 * r + k - b := by omega
  have c5 : (2 * r + k - b = 2 * r + k - a + 1) ↔ (b + 1 = a) := by omega
  have c6 : ¬(2 * r + k - a ≤ r + k) := by omega
  simp only [dpsiP, ps_val, c1, c2, c3, c4, c5, c6, if_false, if_true, and_self, and_false, false_and, and_true]

theorem third_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel E) (ell : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1)) (fun l : Fin m => ps k r l.val)
        (ell + (m : ℂ) - 1) -
      qminor E (fun l : Fin i => ps k r l.val) (fun l : Fin i => ps k r l.val) (ell + (i : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => ps k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => ps k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hu : ell + ((m + 1 : ℕ) : ℂ) - 1 = ell + (m : ℂ) := by push_cast; ring
      rw [hu]
      have hstep : qminor E (fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin (m + 1) => ps k r l.val) (ell + (m : ℂ)) -
          qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin m => ps k r l.val) (ell + (m : ℂ) - 1) ∈ Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E
              ((fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1)) ∘ Fin.castSucc)
              ((fun l : Fin (m + 1) => ps k r l.val) ∘ l.succAbove) (ell + (m : ℂ) - 1))
          (fun l _ => Tm E (ell + (m : ℂ)) (ps k r (m + 1)) (ps k r l.val)) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_line A (2 * r + k + 1) m E hG]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have hne : ps k r (m + 1) ≠ ps k r l.val := by
            intro e
            have := congrArg Fin.val e
            simp only [ps_val] at this
            omega
          have hin : InNp k r (ps k r (m + 1)) (ps k r l.val) := by
            simp only [InNp, ps_val]
            omega
          have hd : dpsiP k r z' (ps k r (m + 1)) (ps k r l.val) = if l.val = m then 1 else 0 := by
            rw [dpsi_last_basis_shift k r z' (m + 1) l.val (by omega) (by omega)]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => ps k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => ps k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

private theorem sR_eq_ps (k r j : ℕ) (hj : j ≤ r) : sR k r j hj = fun l : Fin j => ps k r l.val := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val]

private theorem sR_succAbove_eq_ps (k r m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) :
    (fun l : Fin m => sR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => ps k r (if l.val < i.val then l.val else l.val + 1) := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val, succAbove_val]

theorem third_peeling_identity : PeelingDualColumn := by
  intro A _ _ k r z' E hG m hm i ell
  rw [sR_succAbove_eq_ps, sR_eq_ps, sR_eq_ps]
  exact third_peeling_minor_mem_ideal k r z' E hG ell m i.val (by have := i.isLt; omega) hm

theorem second_peeling_identity : PeelingCovector := by
  intro A _ _ k m z' yb E i u hz'
  have ha : xR k (m + 1) (m + 1) le_rfl = fun l : Fin (m + 1) => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  have hb : (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) =
      fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1) := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE, succAbove_val, pe_val]; all_goals (split_ifs <;> omega)
  have hi : xR k (m + 1) i.val (by have := i.isLt; omega) = fun l : Fin i.val => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  rw [hb, ha, hi]
  have step := peel_col (Ideal.span (rgen k (m + 1) z' E)) E (fun w => herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb)
    (fun l : Fin (m + 1) => pe k (m + 1) l.val) (fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1))
    (wI k (m + 1)) u (herm (Hpk k (m + 1)) z' yb) (by
      intro l
      have := l.isLt
      apply hT_of _ _ _ (fun w => dpsiP k (m + 1) z' (pe k (m + 1) l.val) (wI k (m + 1) w))
      · intro w
        have hw := w.isLt
        have hne : pe k (m + 1) l.val ≠ wI k (m + 1) w := by
          intro h2; have h3 := congrArg Fin.val h2; rw [pe_lt (by omega)] at h3; simp only [wI] at h3; omega
        rw [tm_offdiag _ _ hne]
        apply mem_gen
        simp only [InNp, wI]; rw [pe_lt (by omega)]; omega
      · simp only [dpsi_e_w k (m + 1) z' l.val (by omega), last_iff]
        by_cases hl : l.val = m
        · have e : l.val + 1 = m + 1 := by omega
          simp only [e, if_true, hl]
          rw [herm_wsum k (m + 1) z' yb hz']
          congr 1; ext w; ring
        · have e : ¬ (l.val + 1 = m + 1) := by omega
          simp [e, hl])
  have hc : ((fun l : Fin (m + 1) => pe k (m + 1) l.val) ∘ Fin.castSucc) = fun l : Fin m => pe k (m + 1) l.val := by
    funext l; simp
  rw [hc] at step
  have h2 := smul_mem' _ (herm (Hpk k (m + 1)) z' yb) (first_peeling_minor_mem_ideal k (m + 1) z' E u m i.val (by omega) (by omega))
  have := Ideal.add_mem _ step h2
  rw [smul_sub] at this
  simpa using this

theorem fourth_peeling_identity : PeelingDualCovector := by
  intro A _ _ k m z' yb E hG i ell hz hy
  rw [sR_succAbove_eq_ps, sR_eq_ps, sR_eq_ps]
  have hrow := peel_row (Ideal.span (rgen k (m + 1) z' E)) E hG
    (fun w : Fin (k + 1) => yb (wI k (m + 1) w))
    (fun l : Fin m => ps k (m + 1) (if l.val < i.val then l.val else l.val + 1)) (wI k (m + 1))
    (fun l : Fin (m + 1) => ps k (m + 1) l.val) (ell + (m : ℂ)) (herm (Hpk k (m + 1)) yb z') ?_
  · have hp := third_peeling_minor_mem_ideal k (m + 1) z' E hG ell m i.val (by have := i.isLt; omega) le_rfl
    have hsm := smul_mem' (Ideal.span (rgen k (m + 1) z' E)) (herm (Hpk k (m + 1)) yb z') hp
    simp only [Function.comp_def, Fin.coe_castSucc] at hrow
    have hsum := (Ideal.span (rgen k (m + 1) z' E)).add_mem hrow hsm
    rw [smul_sub, sub_add_sub_cancel] at hsum
    exact hsum
  · intro l
    refine hT_of _ _ _ (fun w => dpsiP k (m + 1) z' (wI k (m + 1) w) (ps k (m + 1) l.val)) _ ?_ ?_
    · intro w
      have hl := l.isLt
      have hw : (wI k (m + 1) w).val = m + 1 + w.val := rfl
      have hwk := w.isLt
      have hne : wI k (m + 1) w ≠ ps k (m + 1) l.val := by
        intro e
        have := congrArg Fin.val e
        simp only [ps_val, hw] at this
        omega
      have hin : InNp k (m + 1) (wI k (m + 1) w) (ps k (m + 1) l.val) := by
        simp only [InNp, ps_val, hw]
        omega
      rw [tm_offdiag _ _ hne]
      exact mem_gen hin
    · simp only [dpsi_middle_last_basis k (m + 1) z' l.val l.isLt]
      by_cases hlm : l = Fin.last m
      · have hv : l.val + 1 = m + 1 := by rw [hlm, Fin.val_last]
        rw [if_pos hlm]
        simp only [hv, if_true]
        rw [herm_wsum k (m + 1) yb z' hy]
      · have hv : ¬ (l.val + 1 = m + 1) := fun e => hlm (Fin.ext (by rw [Fin.val_last]; omega))
        rw [if_neg hlm]
        simp only [hv, if_false, mul_zero, Finset.sum_const_zero]

theorem peeling_of_parts : PeelOfParts := fun _ => ⟨first_peeling_identity, second_peeling_identity, third_peeling_identity, fourth_peeling_identity⟩

end Formalism.FourierDecayAlt.P.SignAntidiagonal
