import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PosIffLtNP

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMS

open PI.FJM PI.FJMP

theorem pos_of_sign {x : ℚ} {b : Bool} (hb : b = true) (h : b = true ↔ 0 < x) : 0 < x := h.mp hb

theorem neg_of_sign {x : ℚ} {b : Bool} (hb : b = false) (h0 : x ≠ 0) (h : b = true ↔ 0 < x) : x < 0 := by
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · exact hlt
  · exact absurd (h.mpr hgt) (by rw [hb]; decide)

theorem segs_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : SegFacts p q r s μ μ' :=
  segJ_of leftDiagonalActionFormula rightDiagonalActionFormula leftOffDiagonalActionFormula rightOffDiagonalActionFormula p q r s μ μ' P hM

theorem hypothesis_first_cover : HypA := by
  intro p q r s μ μ' P hM
  obtain ⟨sL1p, -, -, -, sL2p, -, -, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inl (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inl (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inl_injective.comp (Fin.castLE_injective _)) (Sum.inl_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightFirst p q r s μ) sL1p i) (fun k => pos_of_lt (rightWeightFirst p q r s μ') sL2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightFirst p q r s μ') sL2p c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_third_cover : HypC := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, sR1p, -, -, -, sR2p, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inr (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inr (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inr_injective.comp (Fin.castLE_injective _)) (Sum.inr_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightSecond p q r s μ) sR1p i) (fun k => pos_of_lt (rightWeightSecond p q r s μ') sR2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightSecond p q r s μ') sR2p c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a h2
      exact ⟨x, by simp only [hx]⟩

theorem hypothesis_second_cover : HypB := by
  intro p q r s μ μ' P hM
  obtain ⟨-, sL1n, -, -, -, -, -, sR2n⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightFirst p q r s μ) sL1n i) (fun k => neg_of_lt (rightWeightSecond p q r s μ') sR2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightFirst p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightSecond p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightSecond p q r s μ') sR2n c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_fourth_cover : HypD := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, -, sR1n, -, sL2n, -, -⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightSecond p q r s μ) sR1n i) (fun k => neg_of_lt (rightWeightFirst p q r s μ') sL2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightSecond p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightFirst p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightFirst p q r s μ') sL2n c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a h2
      exact ⟨x, by simp only [hx]⟩

theorem cover_by_blocks : CoverJ := by
  intro p q r s μ μ' P hM e he l hl
  obtain ⟨sL1p, sL1n, sR1p, sR1n, sL2p, sL2n, sR2p, sR2n⟩ := segs_of hM
  obtain ⟨h1, h2, h3, h4⟩ := pure_of hM he hl
  rcases l with ⟨a | a, c | c⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightFirst p q r s μ') sL2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inl (Or.inl ⟨(x, y), by simp only [ιA, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightSecond p q r s μ') sR2n c (neg_of_sign rfl h2 h4)
    exact Or.inl (Or.inl (Or.inr ⟨(x, y), by simp only [ιB, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightFirst p q r s μ') sL2n c (neg_of_sign rfl h2 h4)
    exact Or.inr ⟨(x, y), by simp only [ιD, hx, hy]⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightSecond p q r s μ') sR2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inr ⟨(x, y), by simp only [ιC, hx, hy]⟩)

theorem intFacts_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : IntFacts p q r s μ μ' := by
  obtain ⟨e0, he0⟩ := exists_mem_support hM.2.1
  refine ⟨fun a => ?_, fun c => ?_⟩
  · rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula (mem_leftHighestWeight_of_isMinimalJointVector hM) e0 he0 a, Int.floor_intCast]
  · rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula (mem_rightHighestWeight_of_isMinimalJointVector hM) e0 he0 c, Int.floor_intCast]

end PI.FJMS
