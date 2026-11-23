import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondEmbeddingInjective

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def Marked (o : Finset (Fin (D.nB j + D.r))) : Prop := ∃ l ∈ o, l.val < D.nB j

open Classical in

def fk (o : Finset (Fin (D.nB j + D.r))) : Fin (D.nB j + D.r) → D.ML :=
  if D.Marked j o then D.e1 j else D.e0 j

theorem fk_inj (o : Finset (Fin (D.nB j + D.r))) : Function.Injective (D.fk j o) := by
  unfold fk; split_ifs
  · exact D.second_embedding_injective j
  · exact D.index_embedding_injective j

theorem segL_fk (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) :
    D.SegL j (D.fk j o l) := by
  unfold fk; split_ifs
  · exact D.segment_letter_second_embedding j l
  · exact D.segment_letter_first_embedding j l

theorem fk_castAdd (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.fk j o (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  unfold fk; split_ifs <;> simp

def cnt (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : ℕ :=
  ∑ l, if D.fk j o l = i then (if l ∈ o then 1 else 0) else 0

theorem cnt_eq (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (l0 : Fin (D.nB j + D.r))
    (h : D.fk j o l0 = i) : D.cnt j o i = if l0 ∈ o then 1 else 0 := by
  unfold cnt
  rw [Finset.sum_eq_single l0]
  · rw [if_pos h]
  · intro l _ hl
    rw [if_neg]
    intro h2
    exact hl (D.fk_inj j o (h2.trans h.symm))
  · intro h2; exact absurd (Finset.mem_univ _) h2

theorem cnt_zero (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (h : ∀ l, D.fk j o l ≠ i) :
    D.cnt j o i = 0 := by
  unfold cnt
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem cnt_le_one (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : D.cnt j o i ≤ 1 := by
  by_cases h : ∃ l, D.fk j o l = i
  · obtain ⟨l0, h0⟩ := h
    rw [D.cnt_eq j o i l0 h0]
    split_ifs <;> simp
  · push_neg at h
    rw [D.cnt_zero j o i h]; exact Nat.zero_le _

theorem first_embedding_ne_tangent (l : Fin (D.nB j + D.r)) (t : D.Tau) : D.e0 j l ≠ D.mtp t := by
  refine Fin.addCases (fun a => ?_) (fun m => ?_) l <;> simp [mb, mlab, mtp]

theorem second_embedding_tangent_index (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mtp (j, m)) :
    m.val ≠ 0 ∧ l = Fin.natAdd (D.nB j) (Fin.rev m) := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mtp]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · simp [mlab, mtp]
    · intro h
      simp only [mtp, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨h0, by rw [Fin.rev_rev]⟩

theorem second_embedding_label_index_zero (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mlab (j, m)) :
    m.val = 0 := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mlab]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · intro h
      simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact h0
    · simp [mlab, mtp]

theorem cnt_mb (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.cnt j o (D.mb (D.eB j a)) = if Fin.castAdd D.r a ∈ o then 1 else 0 :=
  D.cnt_eq j o _ _ (D.fk_castAdd j o a)

theorem cnt_lab_add_tp (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mlab (j, m)) + D.cnt j o (D.mtp (j, m)) =
      if Fin.natAdd (D.nB j) (Fin.rev m) ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · have hf : D.fk j o = D.e1 j := by unfold fk; rw [if_pos hM]
    by_cases h0 : m.val = 0
    · rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_pos h0]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact (D.second_embedding_tangent_index j l m hl).1 h0), add_zero]
    · rw [D.cnt_eq j o (D.mtp (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_neg h0]),
        D.cnt_zero j o (D.mlab (j, m)) (by
          intro l hl; rw [hf] at hl; exact h0 (D.second_embedding_label_index_zero j l m hl)), zero_add]
  · have hf : D.fk j o = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, first_embedding_natAdd, Fin.rev_rev]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact D.first_embedding_ne_tangent j l _ hl), add_zero]

theorem cnt_tp_zero (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) (h0 : m.val = 0) :
    D.cnt j o (D.mtp (j, m)) = 0 := by
  apply D.cnt_zero
  intro l hl
  unfold fk at hl
  split_ifs at hl
  · exact (D.second_embedding_tangent_index j l m hl).1 h0
  · exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_tp_le (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mtp (j, m)) ≤ ∑ a : Fin (D.nB j), if Fin.castAdd D.r a ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · obtain ⟨l, hl, hln⟩ := hM
    refine le_trans (D.cnt_le_one j o _) ?_
    have : (if Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) ∈ o then 1 else 0 : ℕ) = 1 := by
      rw [if_pos]
      have : Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) = l := by ext; simp
      rw [this]; exact hl
    have h2 := Finset.single_le_sum (f := fun a : Fin (D.nB j) => if Fin.castAdd D.r a ∈ o then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨l.val, hln⟩ : Fin (D.nB j)))
    simp only [this] at h2
    exact h2
  · rw [D.cnt_zero j o]
    · exact Nat.zero_le _
    · intro l hl
      unfold fk at hl
      rw [if_neg hM] at hl
      exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_not_segL (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (hi : ¬ D.SegL j i) :
    D.cnt j o i = 0 := by
  apply D.cnt_zero
  intro l hl
  exact hi (hl ▸ D.segL_fk j o l)

def PsiP {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) : MvPolynomial (D.ML × Fin D.r) K :=
  ∏ k, rename (Prod.map (D.fk j (occ k)) id) (col k)

theorem PsiP_HomD {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0)) :
    HomD (fun i => ∑ k, D.cnt j (occ k) i) (D.PsiP j col occ) := by
  unfold PsiP
  refine HomD_prod _ _ _ fun k _ => ?_
  exact HomD_rename (D.fk j (occ k)) (D.fk_inj j _) _ _ ((mem_PolK_iff _ _).mp (hcol k))

theorem PsiP_support {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (hcount : ∀ i, (univ.filter fun k => i ∈ occ k).card = D.dO (D.eA j i))
    (ξ : D.EM) (hξ : ξ ∈ (D.PsiP j col occ).support) :
    D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := by
  have hd := D.PsiP_HomD j col occ hcol ξ hξ
  have hc : ∀ i, (∑ k, if i ∈ occ k then 1 else 0) = D.dO (D.eA j i) := by
    intro i; rw [← hcount i, Finset.card_filter]
  have hz : ∀ i, ldeg ξ i = 0 → ∀ a, ξ (i, a) = 0 := by
    intro i h a
    unfold ldeg at h
    exact (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨a, rfl⟩ := D.eB_surj j b hb
    rw [hd]
    simp only [cnt_mb]
    rw [hc, eA_castAdd]; rfl
  · intro m
    rw [hd, hd, ← Finset.sum_add_distrib]
    simp only [cnt_lab_add_tp]
    rw [hc, eA_natAdd, Fin.rev_rev]; rfl
  · intro m
    rw [hd]
    refine le_trans (Finset.sum_le_sum fun k _ => D.cnt_tp_le j (occ k) m) ?_
    rw [Finset.sum_comm, dLL_eq_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
    rw [hc, eA_castAdd]; rfl
  · intro m h0
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_tp_zero j _ m h0
  · intro i hi
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_not_segL j _ i hi

end TwistData

end Formalism.MainNotions.PlaneGram
