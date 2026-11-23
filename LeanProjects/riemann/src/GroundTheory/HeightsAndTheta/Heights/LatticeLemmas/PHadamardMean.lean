import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Extension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField Matrix GroundTheory.Heights₂.Heights

noncomputable section

section GramHadamard

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem norm_sub_starProjection_le {ι : Type*} [Fintype ι] (v : ι → V) (y : V) :
    ‖y - (Submodule.span ℂ (Set.range v)).starProjection y‖ ≤ ‖y‖ := by
  set U := Submodule.span ℂ (Set.range v)
  calc ‖y - U.starProjection y‖ ≤ ‖y - ((0 : U) : V)‖ := by
        rw [Submodule.starProjection_minimal]
        exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (0 : U)
    _ = ‖y‖ := by simp

theorem re_det_gram_le_prod_fin : ∀ (n : ℕ) (c : Fin n → V),
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : c ∘ e = Sum.elim (fun i ↦ c i.castSucc) (fun _ : Unit ↦ c (Fin.last n)) := by
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : det (gram ℂ c) = det (gram ℂ fun i : Fin n ↦ c i.castSucc) *
        ((‖c (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ c i.castSucc)).starProjection
          (c (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      rw [← det_gram_comp_equiv e c, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key, Complex.re_mul_ofReal, Fin.prod_univ_castSucc]
    exact mul_le_mul (ih _)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ _) 2) (sq_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)

theorem re_det_gram_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → V) :
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_le_prod_fin (Fintype.card ι) (c ∘ e)
  rw [det_gram_comp_equiv e c] at h
  refine h.trans_eq ?_
  exact Fintype.prod_equiv e _ _ fun _ ↦ rfl

end GramHadamard

theorem HadamardMean.intersectionNumber_baseChange : HadamardMean.Statement := by
  intro K _ _ M ι _ x hx hcard
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hx hcard, degreeWith]
  refine (div_le_div_iff_of_pos_right hn).mpr ?_
  have hσ : ∀ σ : K →+* ℂ,
      Real.log (gramDet M.metric σ x) ≤ 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
    intro σ
    have hne : ∀ i, fibreVec M.metric σ (x i) ≠ 0 := fun i ↦
      (linearIndependent_fibreVec M.metric σ hx).ne_zero i
    have h1 : gramDet M.metric σ x ≤ ∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2 :=
      re_det_gram_le_prod _
    calc Real.log (gramDet M.metric σ x)
        ≤ Real.log (∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2) :=
          Real.log_le_log (gramDet_pos M.metric σ hx) h1
      _ = ∑ i, Real.log (‖fibreVec M.metric σ (x i)‖ ^ 2) := by
          rw [Real.log_prod]
          intro i _
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne i))
      _ = 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Real.log_pow, HermitianBundle.normAt]
          push_cast
          rfl
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      2 * ∑ i, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x i)) := by
    rw [Finset.sum_comm (f := fun i σ ↦ Real.log (M.normAt σ (x i))), Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ ↦ hσ σ
  have hc := Real.log_natCast_nonneg
    (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x)))
  linarith

theorem HadamardMean.proof (_h1 : Sublattice.Statement) : HadamardMean.Statement :=
  HadamardMean.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
