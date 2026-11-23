import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondEmbeddingTangentIndex

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem PsiP_integral {v : AddValuation K (WithTop ℚ)} {nc : ℕ}
    (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) (h : Integral v (∏ k, col k)) :
    Integral v (D.PsiP j col occ) :=
  integral_prod_rename col (fun k => Prod.map (D.fk j (occ k)) id)
    (fun k => (D.fk_inj j (occ k)).prodMap Function.injective_id) h

theorem ph_X_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.fk j o l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold fk ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · split_ifs <;> simp [mb]
  · split_ifs
    · rw [second_embedding_natAdd]
      split_ifs <;> simp [mlab, mtp]
    · simp [mlab]

theorem substitution_X_first_embedding (p : ℕ) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.e0 j l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · simp [mb]
  · simp [mlab]

theorem ph_rename_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r)))
    (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.fk j o) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.fk j o) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.ph_X_fk j p o l a
  exact DFunLike.congr_fun this G

theorem substitution_rename_first_embedding (p : ℕ) (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.e0 j) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.substitution_X_first_embedding j p l a
  exact DFunLike.congr_fun this G

theorem PsiP_ph (p : ℕ) {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) :
    D.ph p (D.PsiP j col occ) = rename (Prod.map (D.eA j) id) (∏ k, col k) := by
  unfold PsiP
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => D.ph_rename_fk j p _ _

theorem card_unmarked (o : Finset (Fin (D.nB j + D.r))) (hM : ¬ D.Marked j o) (m : Fin D.r) :
    (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card < D.r := by
  have h1 : (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card ≤
      (Finset.Ico (D.nB j) (D.stg j m)).card := by
    refine Finset.card_le_card_of_injOn (fun l => l.val) ?_ ?_
    · intro l hl
      have hl' := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, hl'.2.1⟩
      by_contra hlt
      exact hM ⟨l, hl'.1, not_le.mp hlt⟩
    · intro x _ y _ h
      exact Fin.ext h
  rw [Nat.card_Ico] at h1
  have := m.2
  have h2 : D.stg j m - D.nB j < D.r := by unfold stg; omega
  omega

theorem PsiP_val {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (cidx : Fin nc → ℤ) (hts : Fin nc → ℕ) (m : Fin D.r)
    (h14 : ∀ k, 1 ≤ cidx k →
      hts k ≤ ((occ k).filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card)
    (h16 : ∀ k, ((colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) (col k)) :
    ((∑ k, colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS D.msg (D.YPset j m) (D.PsiP j col occ) := by
  unfold PsiP
  refine le_trans ?_ (valS_prod_le D.msg (D.YPset j m) Finset.univ _)
  rw [WithTop.coe_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hM : D.Marked j (occ k)
  · have hf : D.fk j (occ k) = D.e1 j := by unfold fk; rw [if_pos hM]
    rw [hf, valS_rename (D.e1 j) (D.second_embedding_injective j), YP_preimage1]
    have : D.msg ∘ D.e1 j = D.msg ∘ D.e0 j := funext fun l => D.second_embedding_mark_eq_first j l
    rw [this]
    exact h16 k
  · have hf : D.fk j (occ k) = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [hf, valS_rename (D.e0 j) (D.index_embedding_injective j)]
    have h0 : (0 : WithTop ℤ) ≤ valS (D.msg ∘ D.e0 j)
        ((D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) (col k) := by
      apply valS_nonneg_of_free
      intro α hα i hi a
      have hlt := D.YP_preimage0 j m i hi
      have hi2 : i ∉ occ k := fun h => hM ⟨i, h, hlt⟩
      have hd := (mem_PolK_iff _ _).mp (hcol k) α hα i
      rw [if_neg hi2] at hd
      unfold ldeg at hd
      exact (Finset.sum_eq_zero_iff.mp hd) a (Finset.mem_univ a)
    refine le_trans ?_ h0
    have : colVal (cidx k) (hts k) D.r ≤ 0 := by
      unfold colVal
      by_cases hc : 1 ≤ cidx k
      · have h1 := h14 k hc
        have h2 := D.card_unmarked j (occ k) hM m
        have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := by
          rintro ⟨-, h⟩; omega
        rw [if_neg h3]
        split_ifs <;> simp
      · have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := fun h => hc h.1
        rw [if_neg h3]
        split_ifs <;> simp
    exact_mod_cast this

end TwistData

end Formalism.MainNotions.PlaneGram
