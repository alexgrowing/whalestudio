import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.SplitInvInjective

open Matrix

noncomputable section

namespace PI.QnLevBasicsW

open Formalism.QuantumDeterminants

variable {k i r' : ℕ}

theorem ιLev_apply_in (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (a b : Fin (2 * r' + k + 1))
    (hp : p.val = a.val + i) (hq : q.val = b.val + i) : ιLev k i r' g p q = g a b := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  have h2 : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i := by omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

theorem ιLev_apply_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]

theorem ιLev_apply_in_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]

theorem liftVec_apply_in (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (a : Fin (2 * r' + k + 1)) (hp : p.val = a.val + i) : liftVec k i r' v p = v a := by
  have ha := a.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

theorem liftVec_apply_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by
  simp only [liftVec]
  rw [dif_neg hp]

theorem bvec_lift (a : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1)) (hq : q.val = a.val + i) :
    liftVec k i r' (bvec a) = bvec q := by
  funext p
  have ha := a.isLt
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · rw [liftVec_apply_in (bvec a) p ⟨p.val - i, by omega⟩ (by simp only [Fin.val_mk]; omega)]
    simp only [bvec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [liftVec_apply_out _ p hp]
    simp only [bvec, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem mulVec_bvec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (q p : Fin m) : (M *ᵥ bvec q) p = M p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem col_fix (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (q : Fin (2 * (i + r') + k + 1))
    (h : ∀ a : Fin (2 * r' + k + 1), q.val = a.val + i → g *ᵥ bvec a = bvec a) :
    ιLev k i r' g *ᵥ bvec q = bvec q := by
  by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
  · have hqa : q.val - i < 2 * r' + k + 1 := by omega
    have e : q.val = (⟨q.val - i, hqa⟩ : Fin (2 * r' + k + 1)).val + i := by simp only [Fin.val_mk]; omega
    rw [← bvec_lift ⟨q.val - i, hqa⟩ q e, mulVec_lift, h _ e]
  · funext p
    rw [mulVec_bvec]
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · rw [ιLev_apply_in_out g p q hp hq]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro e
      rw [e] at hp
      exact hq hp
    · rw [ιLev_apply_out g p q hp]
      simp [bvec, Pi.single_apply]

theorem level_group_homomorphism : LevHom := by
  intro k i r'
  refine ⟨?_, fun g h => ?_⟩
  · rw [ιLev_eq, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  · rw [ιLev_eq, ιLev_eq, ιLev_eq, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem level_group_unitary_hermitian : LevUH := by
  intro k i r' g hg
  have hU : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k i r' g)ᴴ * Hpk k (i + r') * ιLev k i r' g = Hpk k (i + r')
  rw [ιLev_eq, Hpk_eq, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hU]

theorem level_group_nilpotent : LevN := by
  intro k i r' g hg
  simp only [Nset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, h2, h3⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, ?_, ?_⟩
  · intro a p hap
    have ha := a.isLt
    by_cases hai : i ≤ a.val
    · have hbr : a.val - i < r' := by omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · have hpl : p.val - i < 2 * r' + k + 1 := by omega
        rw [ιLev_apply_in g p (eI k (i + r') a) ⟨p.val - i, hpl⟩ (eI k r' ⟨a.val - i, hbr⟩)
          (by simp only [Fin.val_mk]; omega) (by simp only [eI, Fin.val_mk]; omega)]
        rw [h2 ⟨a.val - i, hbr⟩ ⟨p.val - i, hpl⟩ (by simp only [Fin.val_mk]; omega)]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
    · have hq : ¬ (i ≤ (eI k (i + r') a).val ∧ (eI k (i + r') a).val < 2 * r' + k + 1 + i) := by
        simp only [eI, Fin.val_mk]; omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · rw [ιLev_apply_in_out g p _ hp hq]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
  · intro p q hq1 hq2 hp1
    have hql : q.val - i < 2 * r' + k + 1 := by omega
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have hpl : p.val - i < 2 * r' + k + 1 := by omega
      rw [ιLev_apply_in g p q ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      rw [h3 ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      simp only [Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [ιLev_apply_out g p q hp]

theorem level_group_unitary_weyl : LevUW := by
  intro k i r' z g hg
  simp only [UWset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix, hz⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, fun a => ⟨?_, ?_⟩, ?_⟩
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hbr : b.val < r' := by simp only [eI, Fin.val_mk] at hb; omega
    have e : b = eI k r' ⟨b.val, hbr⟩ := Fin.ext rfl
    rw [e]
    exact (hfix ⟨b.val, hbr⟩).1
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hb' := b.isLt
    have hai : i ≤ a.val := by simp only [esI, Fin.val_mk] at hb; omega
    have hcr : a.val - i < r' := by omega
    have e : b = esI k r' ⟨a.val - i, hcr⟩ := by
      apply Fin.ext
      simp only [esI, Fin.val_mk] at hb ⊢
      omega
    rw [e]
    exact (hfix ⟨a.val - i, hcr⟩).2
  · rw [mulVec_lift, hz]

theorem level_group_isotropic_vector : LevWb := by
  intro k i r' z hz
  refine ⟨?_, ?_⟩
  · unfold inWb at hz ⊢
    intro p hp
    by_cases hb : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have ha : p.val - i < 2 * r' + k + 1 := by omega
      rw [liftVec_apply_in z p ⟨p.val - i, ha⟩ (by simp only [Fin.val_mk]; omega)]
      exact hz _ (by simp only [Fin.val_mk]; omega)
    · exact liftVec_apply_out z p hb
  · unfold Tz
    rw [herm_lift]

theorem level_group_ellipticity : LevEll := by
  intro k i r' z g
  unfold ell
  rw [Fin.sum_univ_add]
  refine Eq.trans (congrArg (· + _) (Finset.sum_eq_zero ?_)) ?_
  · intro a _
    have ha := a.isLt
    have hp : ¬ (i ≤ (eI k (i + r') (Fin.castAdd r' a)).val ∧
        (eI k (i + r') (Fin.castAdd r' a)).val < 2 * r' + k + 1 + i) := by
      simp only [eI, Fin.val_mk, Fin.coe_castAdd]; omega
    split_ifs with h
    · rw [ιLev_apply_out g _ _ hp, if_neg]
      intro e
      have := congrArg Fin.val e
      simp only [eI, Fin.val_mk, Fin.coe_castAdd] at this
      omega
    · rw [mulVec_lift, liftVec_apply_out _ _ hp]
  · rw [zero_add]
    apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    split_ifs with h1 h2 h3
    · apply ιLev_apply_in <;> simp only [eI, Fin.val_mk, Fin.coe_natAdd] <;> omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · rw [mulVec_lift]
      apply liftVec_apply_in
      simp only [eI, Fin.val_mk, Fin.coe_natAdd]
      omega

theorem qnLevBasics_main :
    LevHom ∧ LevUH ∧ LevN ∧ LevUW ∧ LevWb ∧ LevEll :=
  ⟨level_group_homomorphism, level_group_unitary_hermitian, level_group_nilpotent, level_group_unitary_weyl, level_group_isotropic_vector, level_group_ellipticity⟩

end PI.QnLevBasicsW
