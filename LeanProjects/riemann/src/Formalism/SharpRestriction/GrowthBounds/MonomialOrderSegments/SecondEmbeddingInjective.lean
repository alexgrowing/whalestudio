import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.IntegralMonomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem mem_initSet (N i : ℕ) (k : Fin N) : k ∈ initSet N i ↔ k.val < i := by
  simp [initSet]

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def nB : ℕ := (D.LLj j).card

def eB (a : Fin (D.nB j)) : D.Lb := ((D.LLj j).equivFin.symm a).1

theorem seg_eB (a : Fin (D.nB j)) : D.seg (D.eB j a) = j := by
  unfold eB
  have h : ((D.LLj j).equivFin.symm a).1 ∈ D.LLj j := ((D.LLj j).equivFin.symm a).2
  unfold LLj at h
  exact (Finset.mem_filter.1 h).2

theorem eB_inj : Function.Injective (D.eB j) := by
  intro a b h
  unfold eB at h
  exact (D.LLj j).equivFin.symm.injective (Subtype.ext h)

theorem eB_surj (b : D.Lb) (hb : D.seg b = j) : ∃ a, D.eB j a = b := by
  refine ⟨(D.LLj j).equivFin ⟨b, by simp [LLj, hb]⟩, ?_⟩
  simp [eB]

theorem dLL_eq_sum : D.dLL j = ∑ a, D.dB (D.eB j a) := by
  unfold dLL
  rw [← Finset.sum_coe_sort (D.LLj j)]
  exact (Equiv.sum_comp (D.LLj j).equivFin.symm (fun x => D.dB x.1)).symm

def eA : Fin (D.nB j + D.r) → D.OL :=
  Fin.addCases (motive := fun _ => D.OL) (fun a => Sum.inl (D.eB j a)) (fun m => Sum.inr (j, Fin.rev m))

def e0 : Fin (D.nB j + D.r) → D.ML :=
  Fin.addCases (motive := fun _ => D.ML) (fun a => D.mb (D.eB j a)) (fun m => D.mlab (j, Fin.rev m))

def e1 : Fin (D.nB j + D.r) → D.ML :=
  Fin.addCases (motive := fun _ => D.ML) (fun a => D.mb (D.eB j a))
    (fun m => if (Fin.rev m).val = 0 then D.mlab (j, Fin.rev m) else D.mtp (j, Fin.rev m))

@[simp] theorem eA_castAdd (a : Fin (D.nB j)) : D.eA j (Fin.castAdd D.r a) = Sum.inl (D.eB j a) := by
  simp [eA]
@[simp] theorem eA_natAdd (m : Fin D.r) : D.eA j (Fin.natAdd (D.nB j) m) = Sum.inr (j, Fin.rev m) := by
  simp [eA]
@[simp] theorem first_embedding_castAdd (a : Fin (D.nB j)) : D.e0 j (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  simp [e0]
@[simp] theorem first_embedding_natAdd (m : Fin D.r) : D.e0 j (Fin.natAdd (D.nB j) m) = D.mlab (j, Fin.rev m) := by
  simp [e0]
@[simp] theorem second_embedding_castAdd (a : Fin (D.nB j)) : D.e1 j (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  simp [e1]
@[simp] theorem second_embedding_natAdd (m : Fin D.r) : D.e1 j (Fin.natAdd (D.nB j) m) =
    if (Fin.rev m).val = 0 then D.mlab (j, Fin.rev m) else D.mtp (j, Fin.rev m) := by
  simp [e1]

theorem index_embedding_injective : Function.Injective (D.e0 j) := by
  intro x y h
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left b =>
      simp only [first_embedding_castAdd, mb, Sum.inl.injEq] at h
      rw [D.eB_inj j h]
    | right m => simp [mb, mlab] at h
  | right m =>
    induction y using Fin.addCases with
    | left b => simp [mb, mlab] at h
    | right m' =>
      simp only [first_embedding_natAdd, mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.rev_inj] at h
      rw [h]

theorem second_embedding_injective : Function.Injective (D.e1 j) := by
  intro x y h
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left b =>
      simp only [second_embedding_castAdd, mb, Sum.inl.injEq] at h
      rw [D.eB_inj j h]
    | right m =>
      simp only [second_embedding_castAdd, second_embedding_natAdd] at h
      split_ifs at h <;> simp [mb, mlab, mtp] at h
  | right m =>
    induction y using Fin.addCases with
    | left b =>
      simp only [second_embedding_castAdd, second_embedding_natAdd] at h
      split_ifs at h <;> simp [mb, mlab, mtp] at h
    | right m' =>
      simp only [second_embedding_natAdd] at h
      split_ifs at h <;> simp_all [mlab, mtp]

theorem second_embedding_mark_eq_first (k : Fin (D.nB j + D.r)) : D.msg (D.e1 j k) = D.msg (D.e0 j k) := by
  induction k using Fin.addCases with
  | left a => simp
  | right m =>
    simp only [second_embedding_natAdd, first_embedding_natAdd]
    split_ifs <;> simp [msg, mlab, mtp]

theorem range_first_embedding (i : D.ML) : (∃ k, D.e0 j k = i) ↔
    (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨D.eB j a, D.seg_eB j a, by simp⟩
    | right m => exact Or.inr ⟨Fin.rev m, by simp⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m, rfl⟩)
    · obtain ⟨a, rfl⟩ := D.eB_surj j b hb
      exact ⟨Fin.castAdd D.r a, by simp⟩
    · exact ⟨Fin.natAdd (D.nB j) (Fin.rev m), by simp⟩

theorem segment_letter_first_embedding (k : Fin (D.nB j + D.r)) : D.SegL j (D.e0 j k) := by
  rcases (D.range_first_embedding j _).1 ⟨k, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem segment_letter_second_embedding (k : Fin (D.nB j + D.r)) : D.SegL j (D.e1 j k) := by
  induction k using Fin.addCases with
  | left a => exact Or.inl ⟨D.eB j a, D.seg_eB j a, by simp⟩
  | right m =>
    rw [second_embedding_natAdd]
    split_ifs
    · exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)
    · exact Or.inr (Or.inr ⟨Fin.rev m, rfl⟩)

def stg (m : Fin D.r) : ℕ := D.nB j + (D.r - 1 - m.val)

theorem TL_preimage (m : Fin D.r) :
    (D.TLset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by
  ext k
  simp only [Finset.mem_preimage, mem_initSet]
  induction k using Fin.addCases with
  | left a =>
    have h1 : D.e0 j (Fin.castAdd D.r a) ∈ D.TLset j m := by
      rw [first_embedding_castAdd]
      unfold TLset
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [LLj, seg_eB]))
    have h2 : (Fin.castAdd D.r a).val < D.stg j m := by
      simp only [Fin.coe_castAdd, stg]
      have := a.2
      omega
    exact iff_of_true h1 h2
  | right m' =>
    rw [first_embedding_natAdd]
    have hm := m.2
    have hm' := m'.2
    simp only [TLset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
    rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
    omega

theorem YP_preimage1 (m : Fin D.r) :
    (D.YPset j m).preimage (D.e1 j) (D.second_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by
  ext k
  simp only [Finset.mem_preimage, mem_initSet]
  induction k using Fin.addCases with
  | left a =>
    have h1 : D.e1 j (Fin.castAdd D.r a) ∈ D.YPset j m := by
      rw [second_embedding_castAdd]
      unfold YPset
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [LLj, seg_eB]))
    have h2 : (Fin.castAdd D.r a).val < D.stg j m := by
      simp only [Fin.coe_castAdd, stg]
      have := a.2
      omega
    exact iff_of_true h1 h2
  | right m' =>
    rw [second_embedding_natAdd]
    have hm := m.2
    have hm' := m'.2
    split_ifs with h0
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      constructor
      · intro h
        exact h.elim
      · intro h
        omega
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
      omega

theorem YP_preimage0 (m : Fin D.r) (k : Fin (D.nB j + D.r))
    (hk : k ∈ (D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) : k.val < D.nB j := by
  rw [Finset.mem_preimage] at hk
  induction k using Fin.addCases with
  | left a => simp
  | right m' =>
    rw [first_embedding_natAdd] at hk
    simp [YPset, mb, mlab, mtp] at hk

end TwistData

end Formalism.MainNotions.PlaneGram
