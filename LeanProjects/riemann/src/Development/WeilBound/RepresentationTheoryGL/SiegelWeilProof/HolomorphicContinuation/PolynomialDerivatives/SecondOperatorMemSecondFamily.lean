import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem first_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f : PX m n} (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  unfold D1
  split_ifs with hab ha ha
  · refine (F1 ε).neg_mem ((F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ha]) (partial_deriv_mem_first_family ε _ hf))
  · exact (F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ← hab]; simpa using ha) (partial_deriv_mem_first_family ε _ hf)
  · have hb : ε b = false := by cases h' : ε b <;> simp_all
    refine (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_first_family ε (by simp [inF1, ha]) (variable_mul_mem_first_family ε (by simp [inF1, hb]) hf)
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    exact (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => partial_deriv_mem_first_family ε _ (partial_deriv_mem_first_family ε _ hf))

theorem second_operator_mem_second_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {g : PX m n} (hg : g ∈ F2 ε) : D2 ε c a b g ∈ F2 ε := by
  unfold D2
  split_ifs with hab ha ha
  · exact (F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1, ← hab, ha]) (partial_deriv_mem_second_family ε _ hg)
  · refine (F2 ε).neg_mem ((F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha)
      (partial_deriv_mem_second_family ε _ hg))
  · exact (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => partial_deriv_mem_second_family ε _ (partial_deriv_mem_second_family ε _ hg))
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    refine (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha) (variable_mul_mem_second_family ε (by simp [inF1, hb]) hg)

theorem bf_mono_right (w : (Fin m × Fin n × Bool →₀ ℕ) → ℂ) (p : PX m n) (t : Fin m × Fin n × Bool →₀ ℕ) :
    bf w p (monomial t 1) = p.coeff t * w t := by
  classical
  rw [bf_eq w (p.support ∪ {t}) Finset.subset_union_left ((support_monomial_subset).trans Finset.subset_union_right)]
  rw [Finset.sum_eq_single t]
  · simp [coeff_monomial]
  · intro s _ hs; simp [coeff_monomial, Ne.symm hs]
  · intro h; simp [coeff_monomial]; left; by_contra h'; exact h (Finset.mem_union_left _
      (MvPolynomial.mem_support_iff.mpr h'))

theorem nondeg (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by
  ext s
  rw [coeff_zero]
  by_cases hs : ∀ k ∈ s.support, inF1 ε k
  · have hu := partner_support_second_family ε hs
    have := h0 (s.mapDomain pE) hu
    rw [contr_eq_bf ε c hh (monomial_mem_second_family ε hu 1), rename_monomial, mapDomain_pE_pE, bf_mono_right] at this
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (wt_pos hc s).ne')
  · by_contra hne
    exact hs ((mem_first_family_iff ε h).mp hh s (MvPolynomial.mem_support_iff.mpr hne))

theorem Bop_box (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, Bop ε c Λ f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => Bop ε c Λ x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    rw [Bop_mono]
    unfold Bm
    rw [if_pos hs]
    refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨htF, htr⟩ := (mem_cand ε _ t).mp ht
    exact ⟨t, htF, by rw [htr]; exact hR, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

end CoreC

open CoreC in
theorem repB : RepB := by
  intro m n ε c hc Λ hΛ
  refine ⟨Bop ε c Λ, fun R f hf => Bop_box ε c Λ R f hf, fun f hf g hg => functional_representation_by_contraction ε hc Λ hΛ hf hg, ?_⟩
  intro a b f hf
  have hB1 : Bop ε c Λ (D1 ε c a b f) ∈ F1 ε := representing_operator_mem_first_family ε c Λ _
  have hB2 : D1 ε c a b (Bop ε c Λ f) ∈ F1 ε := first_operator_mem_first_family ε c a b (representing_operator_mem_first_family ε c Λ f)
  rw [← sub_eq_zero]
  refine nondeg ε hc (Submodule.sub_mem _ hB1 hB2) fun u hu => ?_
  have hg : (monomial u (1 : ℂ) : PX m n) ∈ F2 ε := monomial_mem_second_family ε hu 1
  rw [sub_mul, contr_sub, ← functional_representation_by_contraction ε hc Λ hΛ (first_operator_mem_first_family ε c a b hf) hg,
    contraction_first_operator_adjoint ε hc a b (representing_operator_mem_first_family ε c Λ f) hg, ← functional_representation_by_contraction ε hc Λ hΛ hf (second_operator_mem_second_family ε c a b hg), sub_neg_eq_add,
    ← map_add, ← dop_split ε c a b hf hg, hΛ]

end PositivityTheory.Rg.Sw.LC
