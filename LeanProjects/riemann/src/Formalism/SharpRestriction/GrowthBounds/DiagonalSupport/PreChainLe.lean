import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosULeIff

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Pl

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n' r : ℕ} [NeZero n']
  {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} (Dt : SignedChainData p O r J)

private theorem ll_mem_preimage_SLt_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j j' : ZMod J) (l : Fin (Dt.nL j')) (t : ℕ) (ht : t < Dt.nL j + r) :
    (ML.ll j' l : ML J Dt.nL r) ∈ mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) t) ↔
      j' = j ∧ l.val < t := by
  simp only [Set.mem_preimage, mlPos, SLt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (segZ j') (Dt.nL j') l.val l.isLt] at h
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') l.val t (by omega) ht).1 h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (segZ j') (Dt.nL j') l.val l.isLt]
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') l.val t (by omega) ht).2 h

private theorem lab_mem_preimage_SLt_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j j' : ZMod J) (m : Fin r) (t : ℕ) (ht : t < Dt.nL j + r) :
    (ML.lab j' m : ML J Dt.nL r) ∈ mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) t) ↔
      j' = j ∧ Dt.nL j + (r - 1 - m.val) < t := by
  simp only [Set.mem_preimage, mlPos, SLt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val)] at h
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ t (by omega) ht).1 h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val)]
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ t (by omega) ht).2 h

private theorem tp_mem_preimage_SLt_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j j' : ZMod J) (m : Fin r) (hm : 1 ≤ m.val) (t : ℕ) (ht : t < Dt.nL j + r) :
    (ML.tp j' m hm : ML J Dt.nL r) ∈ mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) t) ↔
      j' = j ∧ Dt.nL j + (r - 1 - m.val) < t := by
  simp only [Set.mem_preimage, mlPos, SLt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val)] at h
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ t (by omega) ht).1 h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val)]
    exact (posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ t (by omega) ht).2 h

private theorem wc_mem_preimage_SLt_posU_iff (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j j' : ZMod J) (m : Fin r) (t : ℕ) (ht : t < Dt.nL j + r) :
    (ML.wc j' m : ML J Dt.nL r) ∈ mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) t) ↔
      j' + 1 = j := by
  simp only [Set.mem_preimage, mlPos, SLt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · rintro rfl
    refine ⟨rfl, ?_⟩
    exact w_lt_posU' hV hr (segZ (j' + 1)) (Dt.nL (j' + 1)) (hnL _) (r - 1 - m.val) t (by omega) ht

theorem pre_chain (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hch : ∀ j (i : Fin (Dt.nch j)), Dt.chain j i =
      {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val})
    (j : ZMod J) (i : Fin (Dt.nch j)) (hi : i.val ≤ Dt.nL j) :
    mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) i.val) = Dt.chainML j i := by
  have ht : i.val < Dt.nL j + r := by omega
  ext x
  cases x with
  | ll j' l =>
    rw [ll_mem_preimage_SLt_posU_iff Dt hV hnL j j' l i.val ht]
    by_cases hj : j' = j
    · subst hj
      simp only [SignedChainData.chainML, Set.mem_image, hch, Set.mem_union, Set.mem_setOf_eq, true_and]
      constructor
      · intro h
        exact ⟨Sum.inl l, Or.inr ⟨l, rfl, h⟩, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        cases y with
        | inl l' =>
          simp only [SignedChainData.levToML, ML.ll.injEq, heq_eq_eq, true_and] at hyx
          subst hyx
          rcases hy with hy | ⟨l'', hl'', hlt⟩
          · simp at hy
          · cases hl''
            exact hlt
        | inr m => simp [SignedChainData.levToML] at hyx
    · simp only [hj, false_and, false_iff]
      simp only [SignedChainData.chainML, Set.mem_image, not_exists, not_and]
      intro y _ hyx
      cases y with
      | inl l' =>
        simp only [SignedChainData.levToML, ML.ll.injEq] at hyx
        exact hj hyx.1.symm
      | inr m => simp [SignedChainData.levToML] at hyx
  | lab j' m =>
    rw [lab_mem_preimage_SLt_posU_iff Dt hV hnL j j' m i.val ht]
    simp only [SignedChainData.chainML, Set.mem_image]
    constructor
    · rintro ⟨-, h⟩
      omega
    · rintro ⟨y, -, hyx⟩
      cases y <;> simp [SignedChainData.levToML] at hyx
  | tp j' m hm =>
    rw [tp_mem_preimage_SLt_posU_iff Dt hV hnL j j' m hm i.val ht]
    simp only [SignedChainData.chainML, Set.mem_image]
    constructor
    · rintro ⟨-, h⟩
      omega
    · rintro ⟨y, -, hyx⟩
      cases y <;> simp [SignedChainData.levToML] at hyx
  | wc j' m =>
    rw [wc_mem_preimage_SLt_posU_iff Dt hV hr hnL j j' m i.val ht]
    simp only [SignedChainData.chainML, Set.mem_image]
    constructor
    · rintro rfl
      refine ⟨Sum.inr m, Dt.chain_w _ i m, ?_⟩
      simp [SignedChainData.levToML]
    · rintro ⟨y, -, hyx⟩
      cases y with
      | inl l' => simp [SignedChainData.levToML] at hyx
      | inr m' =>
        simp only [SignedChainData.levToML, ML.wc.injEq] at hyx
        rw [← hyx.1]
        ring

private theorem preimage_SLe_posU_eq_preimage_SLt_posU_succ (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r)
    (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j : ZMod J) (u : ℕ) (hu : u < Dt.nL j) :
    mlPos Fr Dt.nL ⁻¹' SLe j (posU Fr (Dt.nL j) (segZ j) u) =
      mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) (u + 1)) := by
  ext x
  cases x with
  | ll j' l =>
    simp only [Set.mem_preimage, mlPos, SLe, SLt, Set.mem_setOf_eq]
    apply and_congr_right
    rintro rfl
    rw [← posU_ll' (segZ j') (Dt.nL j') l.val l.isLt,
      posU_le_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega),
      posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega)]
    omega
  | lab j' m =>
    simp only [Set.mem_preimage, mlPos, SLe, SLt, Set.mem_setOf_eq]
    apply and_congr_right
    rintro rfl
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val),
      posU_le_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega),
      posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega)]
    omega
  | tp j' m hm =>
    simp only [Set.mem_preimage, mlPos, SLe, SLt, Set.mem_setOf_eq]
    apply and_congr_right
    rintro rfl
    rw [← posU_fr' (segZ j') (Dt.nL j') (r - 1 - m.val),
      posU_le_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega),
      posU_lt_iff' hV (segZ j') (Dt.nL j') (hnL j') _ _ (by omega) (by omega)]
    omega
  | wc j' m =>
    simp only [Set.mem_preimage, mlPos, SLe, SLt, Set.mem_setOf_eq]
    apply and_congr_right
    rintro rfl
    exact iff_of_true
      (le_of_lt (w_lt_posU' hV hr _ _ (hnL _) (r - 1 - m.val) u (by omega) (by omega)))
      (w_lt_posU' hV hr _ _ (hnL _) (r - 1 - m.val) (u + 1) (by omega) (by omega))

theorem pre_chain_le (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hch : ∀ j (i : Fin (Dt.nch j)), Dt.chain j i =
      {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val})
    (j : ZMod J) (i : Fin (Dt.nch j)) (u : ℕ) (hiu : i.val = u + 1) (hi : u < Dt.nL j) :
    mlPos Fr Dt.nL ⁻¹' SLe j (posU Fr (Dt.nL j) (segZ j) u) = Dt.chainML j i := by
  rw [preimage_SLe_posU_eq_preimage_SLt_posU_succ Dt hV hr hnL j u hi, ← hiu]
  exact pre_chain Dt hV hr hnL hch j i (by omega)

theorem pre_link (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (j : ZMod J) (mm : Fin r) (hmm : mm.val + 2 ≤ r) :
    mlPos Fr Dt.nL ⁻¹' SLt j (posU Fr (Dt.nL j) (segZ j) (Dt.nL j + (r - 1 - mm.val))) =
      Dt.linkML j mm ∪ {y | ∃ m' : Fin r, mm < m' ∧ y = ML.lab j m'} := by
  have ht : Dt.nL j + (r - 1 - mm.val) < Dt.nL j + r := by omega
  ext x
  cases x with
  | ll j' l =>
    rw [ll_mem_preimage_SLt_posU_iff Dt hV hnL j j' l _ ht]
    simp only [SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, -⟩
      exact Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))
    · rintro (((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m', hm', -, h⟩) | ⟨m', -, h⟩)
      · cases h
      · simp only [ML.ll.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        have := eq_of_heq h2
        subst this
        exact ⟨rfl, by omega⟩
      · cases h
      · cases h
  | lab j' m =>
    rw [lab_mem_preimage_SLt_posU_iff Dt hV hnL j j' m _ ht]
    simp only [SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, h⟩
      refine Or.inr ⟨m, ?_, rfl⟩
      rw [Fin.lt_def]
      omega
    · rintro (((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m', hm', -, h⟩) | ⟨m', hlt, h⟩)
      · cases h
      · cases h
      · cases h
      · simp only [ML.lab.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Fin.lt_def] at hlt
        exact ⟨rfl, by omega⟩
  | tp j' m hm =>
    rw [tp_mem_preimage_SLt_posU_iff Dt hV hnL j j' m hm _ ht]
    simp only [SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, h⟩
      refine Or.inl (Or.inr ⟨m, hm, ?_, rfl⟩)
      rw [Fin.lt_def]
      omega
    · rintro (((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m', hm', hlt, h⟩) | ⟨m', -, h⟩)
      · cases h
      · cases h
      · simp only [ML.tp.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Fin.lt_def] at hlt
        exact ⟨rfl, by omega⟩
      · cases h
  | wc j' m =>
    rw [wc_mem_preimage_SLt_posU_iff Dt hV hr hnL j j' m _ ht]
    simp only [SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      refine Or.inl (Or.inl (Or.inl ⟨m, ?_⟩))
      simp
    · rintro (((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m', hm', -, h⟩) | ⟨m', -, h⟩)
      · simp only [ML.wc.injEq] at h
        rw [h.1]
        ring
      · cases h
      · cases h
      · cases h

theorem ml_letters (hV : Fr.Valid L₁ N₁) (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) :
    (⟨fun i => (LSeg J).vec (mlPos Fr Dt.nL i)⟩ : Letters (ML J Dt.nL r)) = Dt.modelLet := by
  have he : ∀ (z : ℤ) (i : ℕ), i < r → Even (Fr.fr z i) := fun z i hi => (hV.2.2.2.2.1 z i hi).2
  unfold SignedChainData.modelLet
  congr 1
  funext x
  cases x with
  | ll j l => simp [LSeg, mlPos, hsgn]
  | lab j m => simp [LSeg, mlPos, he _ _ (by omega : r - 1 - m.val < r)]
  | wc j m => simp [LSeg, mlPos, he _ _ (by omega : r - 1 - m.val < r)]
  | tp j m hm => simp [LSeg, mlPos, he _ _ (by omega : r - 1 - m.val < r)]

theorem tl_letters (hV : Fr.Valid L₁ N₁) (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) :
    (⟨fun x => (LSeg J).vec (tlPos Fr Dt.nL x)⟩ : Letters (TL J Dt.nL r)) = Dt.trueLet := by
  have he : ∀ (z : ℤ) (i : ℕ), i < r → Even (Fr.fr z i) := fun z i hi => (hV.2.2.2.2.1 z i hi).2
  unfold SignedChainData.trueLet
  congr 1
  funext x
  rcases x with ⟨j, l | m⟩
  · simp [LSeg, tlPos, posTL, hsgn]
  · simp [LSeg, tlPos, posTL, he _ _ (by omega : r - 1 - m.val < r)]

theorem geZ_le {x : WithTop ℤ} {s t : ℝ} (h : s ≤ t) (hx : geZ x t) : geZ x s := by
  intro k hk
  exact h.trans (hx k hk)

variable [NeZero r]

private theorem sDegs_rename_subset_sDegs_preimage {R : Type} [CommRing R] {ι κ : Type} (f : ι → κ) {n : ℕ}
    (LL : Letters κ) (S : Set κ) (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j (rename (fun v : ι × Fin n => (f v.1, v.2)) A) ⊆
      sDegs ⟨fun i => LL.vec (f i)⟩ (f ⁻¹' S) j A := by
  unfold sDegs
  rw [Formalism.MainNotions.SelectionLemmas.twistSub_rename]
  set B := (twistSub ⟨fun i => LL.vec (f i)⟩ (f ⁻¹' S) j) A
  intro k hk
  simp only [Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff] at hk ⊢
  obtain ⟨m, -, hk⟩ := hk
  by_contra hcon
  push_neg at hcon
  apply hk
  rw [B.as_sum, map_sum, coeff_sum]
  simp only [rename_monomial, coeff_monomial]
  have hs : ∀ (s : Finset ((ι × Fin n) →₀ ℕ)) (F : ((ι × Fin n) →₀ ℕ) → GLLaurent R n),
      (∑ x ∈ s, F x).coeff k = ∑ x ∈ s, (F x).coeff k := by
    intro s F
    simp
  rw [hs]
  apply Finset.sum_eq_zero
  intro x hx
  split_ifs
  · exact hcon x (MvPolynomial.mem_support_iff.1 hx)
  · simp

theorem val_of_pre (hV : Fr.Valid L₁ N₁) (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) (S : Set (ZMod J × ℤ)) (T : Set (ML J Dt.nL r))
    (hpre : mlPos Fr Dt.nL ⁻¹' S = T) (t : ℝ)
    (h : geZ (valS Dt.modelLet T (MvPolynomial.map (algebraMap O (KK O)) Go)) t) :
    geZ (valS (LSeg J) S (xiPl Fr O Dt.nL Go)) t := by
  rw [Formalism.MainNotions.G.Joints.StandardMonomialSpace.valS_map (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))] at h
  have hsub : sDegs (LSeg J) S (lastIdx r) (xiPl Fr O Dt.nL Go) ⊆ sDegs Dt.modelLet T (lastIdx r) Go := by
    have hs := sDegs_rename_subset_sDegs_preimage (mlPos Fr Dt.nL) (LSeg J) S (lastIdx r) Go
    rw [hpre, ml_letters Dt hV hsgn] at hs
    exact hs
  have hle : valS Dt.modelLet T Go ≤ valS (LSeg J) S (xiPl Fr O Dt.nL Go) := Finset.inf_mono hsub
  intro k hk
  rw [hk] at hle
  have hne : valS Dt.modelLet T Go ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨k', hk'⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hk'] at hle
  have h1 := h k' hk'.symm
  have h2 : k' ≤ k := WithTop.coe_le_coe.1 hle
  have h3 : (k' : ℝ) ≤ k := by exact_mod_cast h2
  linarith

theorem lam_of_pre {K : ℕ} [NeZero K] (hV : Fr.Valid L₁ N₁)
    (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (S : Set (ZMod J × ℤ)) (T : Set (TL J Dt.nL r))
    (hpre : tlPos Fr Dt.nL ⁻¹' S = T) (M : ℤ)
    (h : lam1S Dt.trueLet T (MvPolynomial.map (algebraMap O (KK O)) No) ≤ ((M : ℤ) : WithBot ℤ)) :
    lam1S (LSeg J) S (xiNo Fr O K Dt.nL No) ≤ ((M : ℤ) : WithBot ℤ) := by
  rw [Formalism.MainNotions.G.Joints.StandardMonomialSpace.lowest_degree_map_of_injective (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))] at h
  have hsub : sDegs (LSeg J) S (0 : Fin K) (xiNo Fr O K Dt.nL No) ⊆ sDegs Dt.trueLet T (0 : Fin K) No := by
    have hs := sDegs_rename_subset_sDegs_preimage (tlPos Fr Dt.nL) (LSeg J) S (0 : Fin K) No
    rw [hpre, tl_letters Dt hV hsgn] at hs
    exact hs
  have hle : lam1S (LSeg J) S (xiNo Fr O K Dt.nL No) ≤ lam1S Dt.trueLet T No := Finset.sup_mono hsub
  exact hle.trans h

end Pl

end Formalism.MainNotions.Proposition5Numerics
