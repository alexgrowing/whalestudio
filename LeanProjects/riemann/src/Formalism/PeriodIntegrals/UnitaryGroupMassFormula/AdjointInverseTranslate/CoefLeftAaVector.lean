import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SubsetUpperHessenberg

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem lx_det_tri {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a b : Fin m, a < b → T a b = 0)
    (hd : ∀ a, T a a = 1) : (T * N).det = N.det := by
  rw [Matrix.det_mul, Matrix.det_of_lowerTriangular T (by
      intro i j hij
      exact hT i j (OrderDual.toDual_lt_toDual.mp hij)), Finset.prod_eq_one (fun a _ => hd a), one_mul]

theorem lx_mulVec_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

theorem lx_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) : (M *ᵥ bvec j) i = M i j := by
  exact (lf_col_of_mulVec rfl i).symm

theorem lx_herm_eI (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [dotProduct, Finset.sum_eq_single (eI k r a)]
  · rw [Pi.star_apply, lf_bvec_apply, if_pos rfl, star_one, one_mul, lx_mulVec_apply,
      Finset.sum_eq_single (esI k r a)]
    · rw [lf_H_eI, if_pos rfl, one_mul]
    · intro q _ hq
      rw [lf_H_eI, if_neg hq, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · intro t _ ht
    rw [Pi.star_apply, lf_bvec_apply, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem lx_sum_red {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (F : Fin n → ℂ)
    (hF : ∀ j, j ∉ Set.range e → F j = 0) : ∑ j, F j = ∑ b, F (e b) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (by intro x _ y _ h; exact he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hF
  rintro ⟨b, rfl⟩
  exact hj (Finset.mem_image_of_mem e (Finset.mem_univ b))

theorem lx_esI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : esI k r b ≠ esI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_esI_val, lf_esI_val] at h2
  have := b.isLt
  have := c.isLt
  omega

theorem lx_eI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : eI k r b ≠ eI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_eI_val, lf_eI_val] at h2
  exact h h2

theorem coef_left_aa : CoefLeftAA := by
  intro k r z m hm s g c hs
  have hrow := subset_row_star k r z s hs
  have inj : Function.Injective (fun b : Fin m => esI k r (Fin.castLE hm b)) := by
    intro b b' h
    have := b.isLt; have := b'.isLt
    have := congrArg Fin.val h
    simp only [lf_esI_val, Fin.val_castLE] at this
    exact Fin.ext (by omega)
  have key : ∀ (a l : Fin m), herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a))) =
      ∑ b : Fin m, s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b)) *
        herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm b))) := by
    intro a l
    simp only [lx_herm_eI]
    rw [← mulVec_mulVec, lx_mulVec_apply]
    refine lx_sum_red (fun b : Fin m => esI k r (Fin.castLE hm b)) inj _ ?_
    intro j hj
    have h0 : s (esI k r (Fin.castLE hm a)) j = 0 := by
      have hc : ∀ b : Fin r, b.val < (Fin.castLE hm a).val → j ≠ esI k r b := by
        intro b hb he
        apply hj
        refine ⟨⟨b.val, by simp only [Fin.val_castLE] at hb; omega⟩, ?_⟩
        rw [he]; rfl
      rw [hrow _ j hc, if_neg]
      intro he; exact hj ⟨a, he.symm⟩
    rw [h0, zero_mul]
  have hM : (Matrix.of fun a l : Fin m => herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
      (Matrix.of fun a b : Fin m => s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b))) *
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) := by
    ext a l
    simp only [of_apply, mul_apply, key]
  rw [hM]
  apply lx_det_tri
  · intro a b hab
    simp only [of_apply]
    have hab' : a.val < b.val := hab
    rw [hrow _ _ ?_, if_neg]
    · exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE]; omega)
    · intro c hc
      exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE] at hc ⊢; omega)
  · intro a
    simp only [of_apply]
    rw [hrow _ _ ?_, if_pos rfl]
    intro c hc
    exact lx_esI_ne k r _ _ (by omega)

theorem coef_left_aa_vector : CoefLeftAAv := by
  unfold CoefLeftAAv
  intro k r z m hm s g B hs _
  have key : (Matrix.of fun a l : Fin m => ((s * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) =
      (Matrix.of fun a b : Fin m => s⁻¹ (eI k r (Fin.castLE hm b)) (eI k r (Fin.castLE hm a))) *
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) := by
    ext a l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, lx_mulVec_apply]
    simp only [lx_mulVec_bvec]
    refine (lx_sum_red (fun b : Fin m => eI k r (Fin.castLE hm b)) ?_
      (fun j => g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a))) ?_).trans ?_
    · intro b b' h
      apply Fin.ext
      have h2 := congrArg Fin.val h
      simp only [lf_eI_val, Fin.coe_castLE] at h2
      exact h2
    · intro j hj
      show g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a)) = 0
      by_cases hle : (Fin.castLE hm a).val ≤ j.val
      · rw [lf_S_invCol k r z s hs (Fin.castLE hm a) j hle, if_neg, mul_zero]
        intro he
        exact hj ⟨a, he.symm⟩
      · exfalso
        apply hj
        push_neg at hle
        simp only [Fin.coe_castLE] at hle
        have := a.isLt
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [lf_eI_val, Fin.coe_castLE, Fin.val_mk]
    · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [key]
  apply lx_det_tri
  · intro a b hab
    have hab' : a.val < b.val := hab
    have hle : (Fin.castLE hm a).val ≤ (eI k r (Fin.castLE hm b)).val := by
      simp only [lf_eI_val, Fin.coe_castLE]
      omega
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ hle,
      if_neg (lx_eI_ne k r _ _ (by simp only [Fin.coe_castLE]; omega))]
  · intro a
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ (lf_eI_val k r _).ge, if_pos rfl]

end AAInvW
