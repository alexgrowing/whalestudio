import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy

noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

theorem cd_mono_factor {m : ℕ} (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (e : σ →₀ ℕ) :
    aeval (killS (offD ι)) (monomial e (1 : ℂ)) =
      (∏ i, X (ι (i, i)) ^ (∑ k : Fin m, e (ι (i, k)))) * aeval (diagOne' ι) (monomial e (1 : ℂ)) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_one, one_mul, one_mul]
  by_cases hoff : ∃ v ∈ e.support, v ∈ offD ι
  · obtain ⟨v, hv, hvo⟩ := hoff
    have h1 : (e.prod fun v k => killS (offD ι) v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [killS, if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    have h2 : (e.prod fun v k => diagOne' ι v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [diagOne', if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    rw [h1, h2, mul_zero]
  · push_neg at hoff
    have hsum : ∀ i, ∑ k : Fin m, e (ι (i, k)) = e (ι (i, i)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        by_contra hne
        exact hoff (ι (i, k)) (Finsupp.mem_support_iff.mpr hne) ⟨i, k, rfl, fun h => hk (Fin.ext h).symm⟩
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hsum]
    have hL : (e.prod fun v k => killS (offD ι) v ^ k) = ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [killS, if_neg (hoff v hv)]
    have hR : (e.prod fun v k => diagOne' ι v ^ k) =
        ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [diagOne', if_neg (hoff v hv)]
      split_ifs <;> simp
    have hsplit : ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v =
        (∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1) *
          ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> simp
    have hF : ∏ v ∈ e.support.filter (fun v => ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k), (X v : MvPolynomial σ ℂ) ^ e v =
        ∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1 := by
      rw [Finset.prod_filter]
    have hinj : Function.Injective (fun i : Fin m => ι (i, i)) := fun a b h => (Prod.mk.inj (hι h)).1
    have himg : ∏ i, (X (ι (i, i)) : MvPolynomial σ ℂ) ^ e (ι (i, i)) =
        ∏ v ∈ Finset.univ.image (fun i : Fin m => ι (i, i)), (X v : MvPolynomial σ ℂ) ^ e v := by
      rw [Finset.prod_image (fun a _ b _ h => hinj h)]
    rw [hL, hR, hsplit, ← hF, himg]
    congr 1
    apply Finset.prod_subset
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨i, k, hik, hk⟩ := hv.2
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [← hik, ← Fin.ext hk]
    · intro v hv hvf
      rw [Finset.mem_image] at hv
      obtain ⟨i, _, rfl⟩ := hv
      have h0 : e (ι (i, i)) = 0 := by
        by_contra hne
        exact hvf (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, i, i, rfl, rfl⟩)
      rw [h0, pow_zero]

theorem diagonal_hypothesis : HypDiag := by
  intro σ m ι hι α P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hm : MvPolynomial.monomial e (P.coeff e) = MvPolynomial.C (P.coeff e) * MvPolynomial.monomial e 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, map_mul, cd_mono_factor ι hι e]
  have hs : ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i := hP e he
  simp only [hs, MvPolynomial.aeval_C]
  ring

theorem diagonal_image_block_free : HypFree := by
  intro σ m n ι hι P
  have hC : ∀ c : ℂ, ∀ e ∈ (MvPolynomial.C c : MvPolynomial σ ℂ).support, ∀ x, e (ι x) = 0 := by
    intro c e he x
    rw [MvPolynomial.C_apply] at he
    have h0 := MvPolynomial.support_monomial_subset he
    rw [Finset.mem_singleton] at h0
    rw [h0]
    rfl
  have hadd : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q + R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hQ e h x
    · exact hR e h x
  have hmul : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q * R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul Q R he)
    rw [Finsupp.add_apply, hQ a ha x, hR b hb x]
  have hgen : ∀ w, ∀ e ∈ (diagOne' ι w).support, ∀ x, e (ι x) = 0 := by
    intro w
    unfold diagOne'
    split_ifs with h1 h2
    · simpa using hC 0
    · simpa using hC 1
    · intro e he x
      have hne : w ≠ ι x := by
        rintro rfl
        obtain ⟨i, k⟩ := x
        by_cases hik : (i : ℕ) = k
        · exact h2 ⟨i, k, rfl, hik⟩
        · exact h1 ⟨i, k, rfl, hik⟩
      rw [MvPolynomial.support_X, Finset.mem_singleton] at he
      rw [he, Finsupp.single_apply, if_neg hne]
  induction P using MvPolynomial.induction_on
  next a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact hC a
  next p q hp hq =>
    rw [map_add]
    exact hadd _ _ hp hq
  next p w hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact hmul _ _ hp (hgen w)

end PI.FJMB
