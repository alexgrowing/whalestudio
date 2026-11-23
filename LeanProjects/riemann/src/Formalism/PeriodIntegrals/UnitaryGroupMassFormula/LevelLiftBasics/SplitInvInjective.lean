import Formalism.FormalDegreeBessel.StatementRP

open Matrix

noncomputable section

namespace PI.QnLevBasicsW

open Formalism.QuantumDeterminants

def splitInv (k i r' : ℕ) : Fin (2 * r' + k + 1) ⊕ Fin (2 * i) → Fin (2 * (i + r') + k + 1)
  | Sum.inl a => ⟨a.val + i, by omega⟩
  | Sum.inr b => ⟨if b.val < i then b.val else b.val + (2 * r' + k + 1), by split_ifs <;> omega⟩

theorem splitInv_inl (k i r' : ℕ) (a : Fin (2 * r' + k + 1)) : (splitInv k i r' (Sum.inl a)).val = a.val + i := rfl

theorem splitInv_inr (k i r' : ℕ) (b : Fin (2 * i)) :
    (splitInv k i r' (Sum.inr b)).val = if b.val < i then b.val else b.val + (2 * r' + k + 1) := rfl

theorem splitInv_injective (k i r' : ℕ) : Function.Injective (splitInv k i r') := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with a | b <;> rcases y with a' | b' <;> simp only [splitInv_inl, splitInv_inr] at hv
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := a.isLt
    have := b'.isLt
    split_ifs at hv <;> omega
  · have := b.isLt
    have := a'.isLt
    split_ifs at hv <;> omega
  · have := b.isLt
    have := b'.isLt
    exact congrArg Sum.inr (Fin.ext (by split_ifs at hv <;> omega))

def split (k i r' : ℕ) : Fin (2 * (i + r') + k + 1) ≃ Fin (2 * r' + k + 1) ⊕ Fin (2 * i) :=
  (Equiv.ofBijective (splitInv k i r') ((Fintype.bijective_iff_injective_and_card _).2
    ⟨splitInv_injective k i r', by simp; omega⟩)).symm

variable {k i r' : ℕ}

theorem split_symm_inl (a : Fin (2 * r' + k + 1)) :
    ((split k i r').symm (Sum.inl a)).val = a.val + i := rfl

theorem split_symm_inr (b : Fin (2 * i)) :
    ((split k i r').symm (Sum.inr b)).val = if b.val < i then b.val else b.val + (2 * r' + k + 1) := rfl

theorem split_in (p : Fin (2 * (i + r') + k + 1)) (a : Fin (2 * r' + k + 1)) (h : p.val = a.val + i) :
    split k i r' p = Sum.inl a := by
  apply (split k i r').symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [split_symm_inl]
  exact h

theorem split_out (p : Fin (2 * (i + r') + k + 1)) (h : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ∃ b, split k i r' p = Sum.inr b := by
  rcases hs : split k i r' p with a | b
  · exfalso
    have hp : p = (split k i r').symm (Sum.inl a) := by rw [← hs, Equiv.symm_apply_apply]
    have hv := congrArg Fin.val hp
    rw [split_symm_inl] at hv
    have := a.isLt
    omega
  · exact ⟨b, rfl⟩

theorem ιLev_eq (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' g = (fromBlocks g 0 0 1).submatrix (split k i r') (split k i r') := by
  ext p q
  rw [Matrix.submatrix_apply]
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  obtain ⟨t, rfl⟩ := (split k i r').symm.surjective q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [ιLev]
  rcases s with a | b <;> rcases t with a' | b'
  · have ha := a.isLt
    have ha' := a'.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    have h2 : i ≤ ((split k i r').symm (Sum.inl a')).val ∧ ((split k i r').symm (Sum.inl a')).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    rw [dif_pos h1, dif_pos h2, fromBlocks_apply₁₁]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, split_symm_inl] <;> omega
  · have ha := a.isLt
    have hb := b'.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    have h2 : ¬(i ≤ ((split k i r').symm (Sum.inr b')).val ∧ ((split k i r').symm (Sum.inr b')).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_pos h1, dif_neg h2, fromBlocks_apply₁₂, Matrix.zero_apply]
  · have hb := b.isLt
    have ha := a'.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, fromBlocks_apply₂₁, Matrix.zero_apply, if_neg]
    intro e
    exact Sum.inr_ne_inl ((split k i r').symm.injective e)
  · have hb := b.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, fromBlocks_apply₂₂, Matrix.one_apply]
    by_cases e : b = b'
    · subst e
      simp
    · have hne : (split k i r').symm (Sum.inr b) ≠ (split k i r').symm (Sum.inr b') :=
        fun h => e (Sum.inr_injective ((split k i r').symm.injective h))
      rw [if_neg hne, if_neg e]

theorem liftVec_eq (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' v = (Sum.elim v 0) ∘ (split k i r') := by
  funext p
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  rw [Function.comp_apply, Equiv.apply_symm_apply]
  simp only [liftVec]
  rcases s with a | b
  · have ha := a.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    rw [dif_pos h1, Sum.elim_inl]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk, split_symm_inl]
    omega
  · have hb := b.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, Sum.elim_inr, Pi.zero_apply]

theorem blocks_mulVec_lift (A : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (J : Matrix (Fin (2 * i)) (Fin (2 * i)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    (fromBlocks A 0 0 J).submatrix (split k i r') (split k i r') *ᵥ liftVec k i r' v =
      liftVec k i r' (A *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [Matrix.fromBlocks_mulVec]
  congr 1
  funext x
  rcases x with x | x <;> simp

theorem mulVec_lift (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' g *ᵥ liftVec k i r' v = liftVec k i r' (g *ᵥ v) := by
  rw [ιLev_eq]
  exact blocks_mulVec_lift g 1 v

theorem dot_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' w) ⬝ᵥ liftVec k i r' v = star w ⬝ᵥ v := by
  rw [liftVec_eq, liftVec_eq]
  simp only [dotProduct, Pi.star_apply, Function.comp_apply]
  rw [Fintype.sum_equiv (split k i r') _ (fun s => star (Sum.elim w 0 s) * Sum.elim v 0 s) (fun _ => rfl)]
  simp [Fintype.sum_sum_type]

def Jrest (k i r' : ℕ) : Matrix (Fin (2 * i)) (Fin (2 * i)) ℂ :=
  (Hpk k (i + r')).submatrix ((split k i r').symm ∘ Sum.inr) ((split k i r').symm ∘ Sum.inr)

theorem Hpk_eq :
    Hpk k (i + r') = (fromBlocks (Hpk k r') 0 0 (Jrest k i r')).submatrix (split k i r') (split k i r') := by
  ext p q
  rw [Matrix.submatrix_apply]
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  obtain ⟨t, rfl⟩ := (split k i r').symm.surjective q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases s with a | b <;> rcases t with a' | b'
  · rw [fromBlocks_apply₁₁]
    have ha := a.isLt
    have ha' := a'.isLt
    have e1 := split_symm_inl (k := k) (i := i) (r' := r') a
    have e2 := split_symm_inl (k := k) (i := i) (r' := r') a'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    have ha := a.isLt
    have hb := b'.isLt
    have e1 := split_symm_inl (k := k) (i := i) (r' := r') a
    have e2 := split_symm_inr (k := k) (i := i) (r' := r') b'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    have hb := b.isLt
    have ha := a'.isLt
    have e1 := split_symm_inr (k := k) (i := i) (r' := r') b
    have e2 := split_symm_inl (k := k) (i := i) (r' := r') a'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₂₂]
    rfl

theorem herm_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' v) (liftVec k i r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [Hpk_eq, blocks_mulVec_lift, dot_lift]

end PI.QnLevBasicsW
