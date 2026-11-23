import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorEqSmulComponent

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pointwise_sum_bound {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (F : (X.Ψ → Fin 2 → Fin 2 → ℂ) → Frame X.Ψ r → ℂ) (T : (X.Ψ → Fin 2 → Fin 2 → ℂ) → ℝ)
    (w S1 : ℝ) (hS10 : 0 ≤ S1) (z0 : Frame X.Ψ r)
    (hexp : ∀ z ∈ X.dom, Summable (fun χ => ‖F χ z‖) → HasSum (fun χ => F χ z) (Q z))
    (hpt : ∀ χ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (F χ) z ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1)
    (hsum : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => Real.exp (-Real.pi * T j.1))) :
    ∀ z ∈ X.dom, X.SameFlag z0 z → X.pnorm la Q z ≤
      2 ^ (w / 2) * (∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1)) * S1 := by
  intro z hz hfl
  have hN := X.pointNorm_nonneg la (fun _ => (1 : ℂ)) z
  have hC : 0 ≤ (2 : ℝ) ^ (w / 2) := by positivity
  have htn : 0 ≤ ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [X.pointNorm_eq_norm_mul la Q z]
  rcases hN.eq_or_lt with hN0 | hNpos
  · rw [← hN0, mul_zero]
    exact mul_nonneg (mul_nonneg hC htn) hS10
  have hpt' : ∀ χ, ‖F χ z‖ * X.pnorm la (fun _ => (1 : ℂ)) z ≤
      2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1 := fun χ => by
    rw [← X.pointNorm_eq_norm_mul la (F χ) z]; exact hpt χ z hz hfl
  have hb : ∀ χ, ‖F χ z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T χ) := by
    intro χ
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [hpt' χ]
  have hzero : ∀ χ, χ ∉ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} → F χ z = 0 := fun χ hχ => by
    by_contra h; exact hχ ⟨z, hz, h⟩
  have hsupp : Function.support (fun χ => ‖F χ z‖) ⊆ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} := by
    intro χ hχ
    by_contra h
    exact hχ (by simp only [hzero χ h, norm_zero])
  have hsumS : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => ‖F j.1 z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hb j.1) (hsum.mul_left _)
  have hsumAll : Summable (fun χ => ‖F χ z‖) := by
    refine (Function.Injective.summable_iff Subtype.val_injective fun χ hχ => ?_).1 hsumS
    rw [norm_eq_zero]
    exact hzero χ fun h => hχ ⟨⟨χ, h⟩, rfl⟩
  have hQ := hexp z hz hsumAll
  have hnorm : ‖Q z‖ ≤ ∑' χ, ‖F χ z‖ := by
    rw [← hQ.tsum_eq]; exact norm_tsum_le_tsum_norm hsumAll
  rw [← tsum_subtype_eq_of_support_subset hsupp] at hnorm
  have hsum2 : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} =>
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T j.1)) :=
    hsum.mul_left _
  have hle : ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, ‖F j.1 z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z *
        ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) := by
    rw [← tsum_mul_left]
    exact hsumS.tsum_le_tsum (fun j => hb j.1) hsum2
  have hm := mul_le_mul_of_nonneg_right (hnorm.trans hle) hN
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hNpos.ne', mul_one] at hm
  linarith

private theorem herm_swap_eq_cc_of_conj_symm {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : herm G y x = cc (herm G x y) := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG' a b]
  ring

private theorem herm_add_smul_self_expand {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (c : E) :
    herm G (x + c • y) (x + c • y) =
      herm G x x + c * herm G y x + cc c * herm G x y + c * cc c * herm G y y := by
  simp only [herm, cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem shortVectorBound_of_coefficient_bounds (h3 : FourierCoefficientProperties (E := E)) (h3q : CuspCoefficientBound (E := E)) (h6p : FlowCoefficientDecay (E := E))
    (h7 : CoefficientIndexLowerBound (E := E)) (h8 : CoefficientHeightBound (E := E)) (h9 : CountingExponentialSum)
    (h10 : IsotropicOutsideLine (E := E)) : ShortVectorBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x hxL hxξ hxE
  have hH0 := hH
  obtain ⟨-, hSS, hiso, hc1, -, -, hw1, -, hχ, hz0, hsup⟩ := hH
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨hep_pos, hep_le, hep_spec⟩ := epsilonZero_spec X c1 w hc1 hw1
  obtain ⟨hxx, α, hx'L, hx'ξ, hucomp, -, hmajNC⟩ :=
    h10 r X ξ hiso z0 hz0 x hxL hxξ hxE fun τ => lt_of_lt_of_le (hcon τ) hep_le
  set x' := x + ((X.NA : E) * (α : E)) • ξ with hx'
  have hx'E : ∀ e : E, x' ≠ e • ξ := by
    intro e he
    exact hxE (e - (X.NA : E) * (α : E)) (by rw [sub_smul, ← he, hx']; abel)
  have hx'x' : herm X.Gm x' x' = 0 := by
    rw [hx', herm_add_smul_self_expand, herm_swap_eq_cc_of_conj_symm X.Gm X.Gm_herm x ξ, hxξ, hiso.2.1, hxx]
    simp [cc]
  obtain ⟨a, hset⟩ := short_vector_setting_exists X hH0 hx'L hx'ξ hx'x' hx'E
  obtain ⟨hpair, hmem⟩ := isotropic_pair_in_lattice X hiso hx'L hx'ξ hx'x' hx'E
  obtain ⟨ε, hε0, hεlt, hεmaj⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧
      ∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x') τ) ≤ ε := by
    let s : Finset ℝ := (Finset.univ.image fun τ => X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ∪
      {flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w / 2}
    have hs : s.Nonempty := ⟨_, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    refine ⟨s.max' hs, lt_of_lt_of_le (half_pos hep_pos)
      (s.le_max' _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))), ?_, fun τ => ?_⟩
    · have hm := s.max'_mem hs
      rcases Finset.mem_union.1 hm with h | h
      · obtain ⟨τ, -, hτ⟩ := Finset.mem_image.1 h
        rw [← hτ]; exact hcon τ
      · rw [Finset.mem_singleton.1 h]; linarith
    · rw [hucomp]
      exact s.le_max' _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
  obtain ⟨hQd, hQb, hQz⟩ := h3q r X ![ξ, (X.NC : E) • x'] hpair hmem la P hSS hχ ν
  have hL3 := h3 r X.toData ![ξ, (X.NC : E) • x'] X.g hpair X.g_pos la (X.fj la ξ ν P) hQd hQb hQz
  have hK : 1 ≤ 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by
    have h1 : 0 < 2 * c1 + 1 := by linarith
    have h2 : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := mul_nonneg (by positivity) h1.le
    linarith
  have hN : (1 : ℝ) ≤ ((4 * fdeg E : ℕ) : ℝ) := by
    have := one_le_field_half_degree (E := E)
    push_cast
    linarith
  have hlow : ∀ j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) *
        ((4 * fdeg E : ℕ) : ℝ)) + ((4 * fdeg E : ℕ) : ℝ) + 2 <
      2 * ∑ τ, (X.chiAt j.1 a τ).re := fun j =>
    lt_of_lt_of_le (hep_spec ε hε0 hεlt) (h7 r X la P ξ ν c1 w z0 x' a ε hset hε0 hεmaj j.1 j.2)
  have hcount : ∀ t0 : ℝ, 1 ≤ t0 →
      {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.Finite ∧
      ({j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.ncard : ℝ) ≤
        ((1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
          (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * t0) ^ ((4 * fdeg E : ℕ) : ℝ) := by
    intro t0 ht0
    obtain ⟨hfin, hcard⟩ := h8 r X la P ξ ν c1 w z0 x' a hset hmajNC t0 ht0
    have hpre : {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0} =
        Subtype.val ⁻¹' {χ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0) ∧
          2 * ∑ τ, (X.chiAt χ a τ).re ≤ t0} := by
      ext j
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    rw [hpre]
    refine ⟨hfin.preimage Subtype.val_injective.injOn, ?_⟩
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
      (fun χ hχ => ⟨⟨χ, hχ.1⟩, rfl⟩), Real.rpow_natCast]
    exact hcard
  have hw0 : 0 ≤ w := le_trans zero_le_one hw1
  obtain ⟨hsumT, hlt⟩ := h9 _ _ w hK hN hw0 ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0}
    (fun j => 2 * ∑ τ, (X.chiAt j.1 a τ).re) hlow hcount
  have hS10 : 0 ≤ sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} :=
    Real.sSup_nonneg fun t ⟨y, _, ht⟩ => ht ▸ X.hatNorm_nonneg la _ y
  have hbound := pointwise_sum_bound X.toData la (X.fj la ξ ν P)
    (fun χ => X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P))
    (fun χ => 2 * ∑ τ, (X.chiAt χ a τ).re) w _ hS10 z0 (hL3 0).2.2
    (fun χ z hz hfl => h6p r X la P ξ ν c1 w z0 x' a hset χ z hz hfl) hsumT
  have hhat : X.hatN la (X.fj la ξ ν P) z0 ≤ 2 ^ (w / 2) *
      (∑' j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
        Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt j.1 a τ).re))) *
      sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} := by
    unfold Data.hatN
    refine csSup_le ⟨_, z0, hz0.1, fun τ => rfl, rfl⟩ ?_
    rintro t ⟨z, hz, hfl, rfl⟩
    exact hbound z hz hfl
  have hm := mul_le_mul_of_nonneg_right hlt.le hS10
  linarith only [hsup, hhat, hm]

end

end ReciprocityTheory.ChartRestriction.G.FD
