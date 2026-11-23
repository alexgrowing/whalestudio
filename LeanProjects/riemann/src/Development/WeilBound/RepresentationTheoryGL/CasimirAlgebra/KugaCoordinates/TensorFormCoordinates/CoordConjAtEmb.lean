import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

section
variable {E : Type} [Field E]

lemma coord_atEmb_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  have h0 := congrArg (coord τ') (atEmb_mul_of_ne h 1 z)
  rwa [map_mul, coord_atEmb, map_zero, one_mul] at h0

lemma coord_conj_atEmb [IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    coord (ComplexEmbedding.conjugate τ) (atEmb τ z) = starRingEnd ℂ z := by
  have : atEmb τ z = atEmb (ComplexEmbedding.conjugate τ) (starRingEnd ℂ z) := by
    rw [atEmb_conj, Complex.conj_conj]
  rw [this, coord_atEmb]

lemma cxkey [IsTotallyComplex E] (τ τ' : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord τ' (atEmb τ 1) - Complex.I * coord τ' (atEmb τ Complex.I)) =
      if τ' = τ then 1 else 0 := by
  by_cases hm : InfinitePlace.mk τ' = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.mp hm with h | h
    · subst h
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have h' : τ' = ComplexEmbedding.conjugate τ := by
        rcases InfinitePlace.mk_eq_iff.mp hm.symm with h2 | h2
        · exfalso
          apply IsTotallyComplex.complexEmbedding_not_isReal τ'
          rw [ComplexEmbedding.isReal_iff, h, h2]
        · exact h2.symm
      have hne : τ' ≠ τ := by
        intro e
        apply IsTotallyComplex.complexEmbedding_not_isReal τ'
        rw [ComplexEmbedding.isReal_iff, h, e]
      rw [if_neg hne, h', coord_conj_atEmb, coord_conj_atEmb, map_one, Complex.conj_I, mul_neg,
        Complex.I_mul_I]
      norm_num
  · have hne : τ' ≠ τ := fun e => hm (by rw [e])
    rw [if_neg hne, coord_atEmb_ne hm, coord_atEmb_ne hm]
    simp

end

lemma half_comb (ι : Type) [Fintype ι] (x x' : ι → ℂ) (y y' : ℂ) :
    (1 / 2 : ℂ) * ((∑ p, x p - y) - Complex.I * (∑ p, x' p - y')) =
      ∑ p, (1 / 2 : ℂ) * (x p - Complex.I * x' p) - (1 / 2 : ℂ) * (y - Complex.I * y') := by
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma half_ite (P : Prop) [Decidable P] (u v : ℂ) :
    (1 / 2 : ℂ) * ((if P then u else 0) - Complex.I * (if P then v else 0)) =
      if P then (1 / 2 : ℂ) * (u - Complex.I * v) else 0 := by
  split_ifs <;> simp

theorem bigCx_holds : BigCx := by
  intro E _ _ _ a Q _ _ lab s
  refine ⟨fun τ i j f => ?_, fun y p p' hp f => ?_⟩
  · have hD : ∀ (z : ℂ) (I J : Q → Fin a), bigD lab s (toL (Matrix.single i j (atEmb τ z))) I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then coord (lab p) (atEmb τ z) else 0) -
          if I = J ∧ i = j then (s : ℂ) * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) else 0 := by
      intro z I J
      simp only [bigD, Matrix.of_apply, toL, Matrix.of_symm_apply, Matrix.single_apply]
      congr 1
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [apply_ite (coord (lab p)), map_zero]
        by_cases h1 : ∀ r, r ≠ p → I r = J r
        · rw [if_pos h1]
          by_cases h4 : i = I p ∧ j = J p
          · rw [if_pos h4, if_pos ⟨h1, h4.1.symm, h4.2.symm⟩]
          · rw [if_neg h4, if_neg (fun h => h4 ⟨h.2.1.symm, h.2.2.symm⟩)]
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      · by_cases h1 : I = J
        · by_cases h2 : i = j
          · subst h2
            rw [if_pos h1, if_pos ⟨h1, rfl⟩]
            congr 1
            refine Finset.sum_congr rfl fun τ' _ => ?_
            simp only [and_self, apply_ite (coord τ'), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          · rw [if_pos h1, if_neg (fun h => h2 h.2)]
            rw [Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => by
              rw [if_neg (fun h => h2 (h.1.trans h.2.symm)), map_zero]]
            simp
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    have hS : (1 / 2 : ℂ) * (∑ τ' : E →+* ℂ, coord τ' (atEmb τ 1) -
        Complex.I * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ Complex.I)) = 1 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [cxkey, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hE : ∀ I J : Q → Fin a, cx τ (bigD lab s) i j I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then (if lab p = τ then (1 : ℂ) else 0) else 0) -
          if I = J ∧ i = j then (s : ℂ) else 0 := by
      intro I J
      simp only [cx, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hD, half_comb, half_ite, cxkey]
      congr 1
      split_ifs
      · linear_combination (s : ℂ) * hS
      · rfl
    have hT : ∀ I : Q → Fin a, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j f I =
        ∑ p, if lab p = τ then (if I p = i then f (Function.update I p j) else 0) else 0 := by
      intro I
      simp [tE, lift, eAt, fib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ <;> by_cases hi : I p = i <;> simp [hl, hi]
    funext I
    simp only [mulVec, dotProduct, hE, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Pi.sub_apply, hT]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ
      · by_cases hi : I p = i
        · rw [Finset.sum_eq_single (Function.update I p j)]
          · have hc : (∀ r, r ≠ p → I r = Function.update I p j r) ∧ I p = i ∧ Function.update I p j p = j :=
              ⟨fun r hr => by rw [Function.update_of_ne hr], hi, by simp⟩
            rw [if_pos hc, if_pos hl, if_pos hl, if_pos hi, one_mul]
          · intro J _ hJ
            rw [if_neg, zero_mul]
            intro h
            exact hJ (Function.eq_update_iff.mpr ⟨h.2.2, fun r hr => (h.1 r hr).symm⟩)
          · intro h
            exact absurd (Finset.mem_univ _) h
        · simp only [if_pos hl, if_neg hi]
          refine Finset.sum_eq_zero fun J _ => ?_
          rw [if_neg (fun h => hi h.2.1), zero_mul]
      · simp only [if_neg hl]
        simp
    · by_cases h : i = j
      · simp [h]
      · simp [h]
  · have hlab : ∀ r, lab (Equiv.swap p p' r) = lab r := by
      intro r
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hp]
      · rw [h2, hp]
      · rfl
    have hM : ∀ I J : Q → Fin a,
        bigM lab s y (I ∘ Equiv.swap p p') (J ∘ Equiv.swap p p') = bigM lab s y I J := by
      intro I J
      simp only [bigM, Matrix.of_apply, Function.comp_apply]
      congr 1
      exact Fintype.prod_equiv (Equiv.swap p p') _ _ (fun r => by rw [hlab])
    let e : (Q → Fin a) ≃ (Q → Fin a) :=
      ⟨fun J => J ∘ Equiv.swap p p', fun J => J ∘ Equiv.swap p p',
        fun J => by funext r; simp, fun J => by funext r; simp⟩
    funext I
    simp only [mulVec, dotProduct, pm, LinearMap.pi_apply, LinearMap.proj_apply]
    exact Fintype.sum_equiv e _ _ (fun J => by simp only [e, Equiv.coe_fn_mk, hM])

end PositivityTheory.Rg.Cz.J
