import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

noncomputable section

namespace UpperTheory.Gal.Gen

private lemma det_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) k) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  classical
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => h _ _)

private lemma det_zero_of_card {k : Type} [Field k] {N ρ : ℕ}
    (A M : Matrix (Fin N) (Fin N) k) (s : Finset (Fin N)) (hr : A.rank ≤ ρ) (hs : ρ < s.card)
    (hM : ∀ i ∈ s, M i = A i) : M.det = 0 := by
  classical
  by_contra hne
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hne
  have heq : (fun i : s => A i) = (fun i => M i) ∘ (fun i : s => (i : Fin N)) := by
    funext i
    exact (hM i i.2).symm
  have hli' : LinearIndependent k (fun i : s => A i) := by
    rw [heq]
    exact hli.comp _ Subtype.val_injective
  have hle : Module.finrank k (Submodule.span k (Set.range (fun i : s => A i))) ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  rw [finrank_span_eq_card hli', Fintype.card_coe] at hle
  omega

private theorem det_add_smul_eq_sum_powerset_pow_card_mul_det {k : Type} [Field k] {N : ℕ} (A B : Matrix (Fin N) (Fin N) k)
    (c : k) :
    (A + c • B).det = ∑ t ∈ (Finset.univ : Finset (Fin N)).powerset,
      c ^ t.card * (Matrix.of fun r j => if r ∈ t then B r j else A r j).det := by
  classical
  rw [← Matrix.det_transpose]
  simp_rw [← Matrix.det_transpose (Matrix.of _)]
  simp only [Matrix.det_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [add_comm (A _ _)]
  rw [Finset.prod_add, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter,
    Finset.prod_mul_distrib, Finset.prod_const, mul_assoc, mul_smul_comm]

theorem detLow_pf : DetLow := by
  intro k _ _ N A B c ρ hA hB hc hr
  classical
  rw [det_add_smul_eq_sum_powerset_pow_card_mul_det]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t _ => ?_
  rw [norm_mul, norm_pow]
  by_cases ht : N - ρ ≤ t.card
  · have h1 := det_norm_le_one (Matrix.of fun r j => if r ∈ t then B r j else A r j) (by
      intro i j
      simp only [Matrix.of_apply]
      split_ifs
      · exact hB i j
      · exact hA i j)
    calc ‖c‖ ^ t.card * ‖(Matrix.of fun r j => if r ∈ t then B r j else A r j).det‖
        ≤ ‖c‖ ^ t.card * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ‖c‖ ^ (N - ρ) := by
        rw [mul_one]
        exact pow_le_pow_of_le_one (norm_nonneg _) hc ht
  · have h0 : (Matrix.of fun r j => if r ∈ t then B r j else A r j).det = 0 := by
      refine det_zero_of_card A _ tᶜ hr ?_ ?_
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · intro i hi
        funext j
        simp only [Matrix.of_apply, if_neg (Finset.mem_compl.mp hi)]
    rw [h0, norm_zero, mul_zero]
    positivity

end UpperTheory.Gal.Gen

end
