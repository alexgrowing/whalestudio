import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Lemmata.GeneralBFactLeftExtra.Imports

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

section Gauss

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _

theorem gauss_abs_le_of_coeff_le (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2

theorem gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]

theorem gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)

theorem finite_place_sum_le {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)

theorem finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  classical
  have hGf := gauss_abs_pos_of_ne_zero w f hf
  have hGg := gauss_abs_pos_of_ne_zero w g hg
  apply le_antisymm
  · refine gauss_abs_le_of_coeff_le w _ (mul_nonneg hGf.le hGg.le) fun u => ?_
    rw [MvPolynomial.coeff_mul]
    refine finite_place_sum_le w _ _ (mul_nonneg hGf.le hGg.le) fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul (coeff_le_gauss_abs w f _) (coeff_le_gauss_abs w g _) (apply_nonneg w _) hGf.le
  ·
    set Sf := f.support.filter (fun s => w (f.coeff s) = gaussAbs w f)
    set Sg := g.support.filter (fun s => w (g.coeff s) = gaussAbs w g)
    have hSf : Sf.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    have hSg : Sg.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w g hg
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image Sf (fun s => m.toSyn s) hSf
    obtain ⟨t0, ht0, ht0max⟩ := Finset.exists_max_image Sg (fun s => m.toSyn s) hSg
    have hfs0 : w (f.coeff s0) = gaussAbs w f := (Finset.mem_filter.1 hs0).2
    have hgt0 : w (g.coeff t0) = gaussAbs w g := (Finset.mem_filter.1 ht0).2
    have hbigf : ∀ s, m.toSyn s0 < m.toSyn s → w (f.coeff s) < gaussAbs w f := by
      intro s hs
      refine lt_of_le_of_ne (coeff_le_gauss_abs w f s) fun heq => ?_
      have hmem : s ∈ Sf := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGf.ne heq
      exact absurd (hs0max s hmem) (not_le.2 hs)
    have hbigg : ∀ t, m.toSyn t0 < m.toSyn t → w (g.coeff t) < gaussAbs w g := by
      intro t ht
      refine lt_of_le_of_ne (coeff_le_gauss_abs w g t) fun heq => ?_
      have hmem : t ∈ Sg := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGg.ne heq
      exact absurd (ht0max t hmem) (not_le.2 ht)
    have hmemu : (s0, t0) ∈ Finset.HasAntidiagonal.antidiagonal (s0 + t0) := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hrest : w (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (s0 + t0)).erase (s0, t0),
        f.coeff x.1 * g.coeff x.2) < gaussAbs w f * gaussAbs w g := by
      refine finite_place_sum_lt w _ _ (mul_pos hGf hGg) fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.1 hx
      have hsum : x.1 + x.2 = s0 + t0 := Finset.HasAntidiagonal.mem_antidiagonal.1 hxmem
      have hsyn : m.toSyn x.1 + m.toSyn x.2 = m.toSyn s0 + m.toSyn t0 := by
        rw [← map_add, ← map_add, hsum]
      rw [map_mul]
      rcases lt_trichotomy (m.toSyn x.1) (m.toSyn s0) with h1 | h1 | h1
      · have h2 : m.toSyn t0 < m.toSyn x.2 := by
          by_contra h2
          have := add_lt_add_of_lt_of_le h1 (not_lt.1 h2)
          rw [hsyn] at this
          exact lt_irrefl _ this
        calc w (f.coeff x.1) * w (g.coeff x.2) ≤ gaussAbs w f * w (g.coeff x.2) :=
              mul_le_mul_of_nonneg_right (coeff_le_gauss_abs w f _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_left (hbigg _ h2) hGf
      · exfalso
        have e1 : x.1 = s0 := m.toSyn.injective h1
        have e2 : x.2 = t0 := by
          rw [e1] at hsum
          exact add_left_cancel hsum
        exact hxne (Prod.ext e1 e2)
      · calc w (f.coeff x.1) * w (g.coeff x.2) ≤ w (f.coeff x.1) * gaussAbs w g :=
              mul_le_mul_of_nonneg_left (coeff_le_gauss_abs w g _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_right (hbigf _ h1) hGg
    have hcoeff : w ((f * g).coeff (s0 + t0)) = gaussAbs w f * gaussAbs w g := by
      rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmemu]
      rw [finite_place_add_eq_of_lt w _ _ (by rwa [map_mul, hfs0, hgt0]), map_mul, hfs0, hgt0]
    rw [← hcoeff]
    exact coeff_le_gauss_abs w _ _

theorem gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg

end Gauss

end ReciprocityTheory.MultiplicativeHeights
