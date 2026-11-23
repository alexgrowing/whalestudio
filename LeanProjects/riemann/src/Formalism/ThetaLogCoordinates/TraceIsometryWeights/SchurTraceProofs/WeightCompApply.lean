import Formalism.ThetaLogCoordinates.TraceIsometryWeights.HasLatBasis

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem single_comp_emb (e : Fin n ↪o Fin r) (a : Fin n) :
    (Pi.single (e a) (1 : ℤ) : Fin r → ℤ) ∘ e = Pi.single a 1 := by
  funext c
  simp only [Function.comp_apply, Pi.single_apply, e.injective.eq_iff]

theorem weight_comp (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun x => (wv LL j x) ∘ e) m = (Finsupp.weight (wv LL j) m) ∘ e := by
  funext a
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

theorem weight_comp_apply (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (m : Fin N × Fin r →₀ ℕ) (a : Fin n) :
    Finsupp.weight (fun x => (wv LL j x) ∘ e) m a = wt LL j (e a) m := by
  rw [weight_comp, Function.comp_apply, weight_wv]

open Formalism.GM.FrozenVariableComponents in
theorem glAct_whe (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (a b : Fin n) {ν : Fin n → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (fun x => (wv LL j x) ∘ e) ν) :
    glAct p LL j (e a) (e b) x ∈ weightedHomogeneousSubmodule ℚ_[p] (fun x => (wv LL j x) ∘ e) (ν + dl a b) := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdw : Finsupp.weight (fun x => (wv LL j x) ∘ e) d = ν := hx (mem_support_iff.mp hd)
  rw [glAct_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · rw [if_pos hij]
    by_cases hv : LL.vec i
    · rw [if_pos hv]
      have := wh_XD (K := ℚ_[p]) (fun x => (wv LL j x) ∘ e) (i, e b) (i, e a) d (coeff d x)
      have e' : ν + dl a b = Finsupp.weight (fun x => (wv LL j x) ∘ e) d - (wv LL j (i, e b)) ∘ e
          + (wv LL j (i, e a)) ∘ e := by
        rw [hdw]; simp only [wv, hij, hv, if_true, dl, single_comp_emb]; abel
      rw [e']; exact this
    · rw [if_neg hv]
      refine Submodule.neg_mem _ ?_
      have := wh_XD (K := ℚ_[p]) (fun x => (wv LL j x) ∘ e) (i, e a) (i, e b) d (coeff d x)
      have hn : ∀ c : Fin n, (-(Pi.single (e c) (1 : ℤ) : Fin r → ℤ)) ∘ e = -Pi.single c 1 := by
        intro c; rw [← single_comp_emb e c]; rfl
      have e' : ν + dl a b = Finsupp.weight (fun x => (wv LL j x) ∘ e) d - (wv LL j (i, e a)) ∘ e
          + (wv LL j (i, e b)) ∘ e := by
        rw [hdw]; simp only [wv, hij, hv, if_true, if_false, Bool.false_eq_true, dl, hn]; abel
      rw [e']; exact this
  · rw [if_neg hij]; exact Submodule.zero_mem _

noncomputable def GAe (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    GlW ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) n where
  E := fun a b => glAct p LL j (e a) (e b)
  comm := fun a b c d x => by
    have := glAct_comm (p := p) LL j (e a) (e b) (e c) (e d) x
    simpa only [e.injective.eq_iff] using this
  comp := fun μ => weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ
  dec := by
    classical
    intro x
    refine ⟨x.support.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)), fun μ hμ => ?_⟩
    apply weightedHomogeneousComponent_eq_zero'
    intro d hd h
    exact hμ (Finset.mem_image.mpr ⟨d, hd, h⟩)
  sum_comp := by
    classical
    intro x S hS
    ext d
    rw [coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have := congrArg (coeff d) (hS _ h)
      rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
      exact this.symm
  idem := by
    classical
    intro μ ν x
    ext d
    by_cases h : μ = ν
    · subst h; simp only [if_true, coeff_weightedHomogeneousComponent]; split_ifs <;> rfl
    · simp only [if_neg h, coeff_zero, coeff_weightedHomogeneousComponent]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h (h1.symm.trans h2))
  diag := by
    classical
    intro c μ x
    rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [glAct_diag_monomial, ← weight_comp_apply, (Finset.mem_filter.mp hd).2]
  shift := by
    classical
    intro a b μ x
    have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)),
        weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x := by
      ext d
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
    conv_lhs => rw [hx]
    rw [map_sum, map_sum]
    have e' : ∀ ν, weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ
        (glAct p LL j (e a) (e b) (weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x)) =
        if ν = μ - dl a b then
          glAct p LL j (e a) (e b) (weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x) else 0 := by
      intro ν
      rw [weightedHomogeneousComponent_of_mem (glAct_whe LL j e a b (weightedHomogeneousComponent_mem _ x ν))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e', Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [weightedHomogeneousComponent_eq_zero', map_zero]
      intro d hd h'
      exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)

theorem GAe_E (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (a b : Fin n) :
    (GAe p LL j e).E a b = glAct p LL j (e a) (e b) := rfl

theorem GAe_comp (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (μ : Fin n → ℤ) :
    (GAe p LL j e).comp μ = weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ := rfl

theorem GAe_isWt_iff (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (μ : Fin n → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GAe p LL j e).IsWt μ x ↔ x ∈ MvPolynomial.restrictSupport ℚ_[p] {m | ∀ a, wt LL j (e a) m = μ a} := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff]
  unfold GlW.IsWt
  rw [GAe_comp]
  constructor
  · intro h m hm a
    have hm' : coeff m x ≠ 0 := mem_support_iff.mp hm
    rw [← h, coeff_weightedHomogeneousComponent] at hm'
    have hw : Finsupp.weight (fun x => (wv LL j x) ∘ e) m = μ := by
      by_contra hne; exact hm' (if_neg hne)
    rw [← weight_comp_apply, hw]
  · intro h
    ext m
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hw
    · rfl
    · by_contra hne
      apply hw
      funext a
      rw [weight_comp_apply]
      exact h (mem_support_iff.mpr (Ne.symm hne)) a

noncomputable def enumC (Cs : Finset (Fin r)) : Fin Cs.card ↪o Fin r := Cs.orderEmbOfFin rfl

theorem enumC_mem (Cs : Finset (Fin r)) (a : Fin Cs.card) : enumC Cs a ∈ Cs :=
  Finset.orderEmbOfFin_mem Cs rfl a

theorem enumC_surj (Cs : Finset (Fin r)) {c : Fin r} (hc : c ∈ Cs) : ∃ a, enumC Cs a = c := by
  have h : c ∈ Set.range (Cs.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact h

theorem wtSpC_iff (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ (GAe p LL j (enumC Cs)).IsWt (la ∘ enumC Cs) x := by
  rw [GAe_isWt_iff, WtSpC]
  have : {m : Fin N × Fin r →₀ ℕ | ∀ c ∈ Cs, wt LL j c m = la c} =
      {m | ∀ a, wt LL j (enumC Cs a) m = (la ∘ enumC Cs) a} := by
    ext m
    constructor
    · intro h a; exact h _ (enumC_mem Cs a)
    · intro h c hc
      obtain ⟨a, rfl⟩ := enumC_surj Cs hc
      exact h a
  rw [this]

theorem hwc_iff (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ HWC p LL j Cs la ↔ (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) x := by
  unfold HWC GlW.IsHW
  rw [Submodule.mem_inf, wtSpC_iff]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, GAe_E]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a b hab
    exact h _ _ ⟨enumC_mem Cs a, enumC_mem Cs b, (enumC Cs).lt_iff_lt.mpr hab⟩
  · rintro h c d ⟨hc, hd, hcd⟩
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    obtain ⟨b, rfl⟩ := enumC_surj Cs hd
    exact h a b ((enumC Cs).lt_iff_lt.mp hcd)

theorem stableC_iff (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) :
    GlStableC p LL j Cs S ↔ (GAe p LL j (enumC Cs)).Stable S := by
  constructor
  · intro h a b x hx
    exact h _ (enumC_mem Cs a) _ (enumC_mem Cs b) x hx
  · intro h c hc d hd x hx
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    obtain ⟨b, rfl⟩ := enumC_surj Cs hd
    exact h a b x hx

theorem isoC_eq (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la =
      (GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) v} := by
  unfold IsoC GlW.gS
  congr 1
  ext S
  simp only [Set.mem_ofPred_eq, stableC_iff]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h v hv; exact h ((hwc_iff LL j Cs la v).mpr hv)
  · intro h v hv; exact h ((hwc_iff LL j Cs la v).mp hv)

theorem exists_ext (Cs : Finset (Fin r)) (μ : Fin Cs.card → ℤ) : ∃ la : Fin r → ℤ, la ∘ enumC Cs = μ :=
  ⟨Function.extend (enumC Cs) μ 0, Function.extend_comp (enumC Cs).injective μ 0⟩

theorem comp_eq_iff (Cs : Finset (Fin r)) (la la' : Fin r → ℤ) :
    la ∘ enumC Cs = la' ∘ enumC Cs ↔ ∀ c ∈ Cs, la c = la' c := by
  constructor
  · intro h c hc
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    exact congrFun h a
  · intro h
    funext a
    exact h _ (enumC_mem Cs a)

theorem GAe_pol_stable (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    (GAe p LL j e).Stable (Pol p r L2) :=
  fun a b _ hx => glAct_pol LL L2 j (e a) (e b) hx

theorem GAe_pol_finW (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    (GAe p LL j e).FinW (Pol p r L2) := by
  classical
  refine ⟨(pol_finite (r := r) L2).toFinset.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)),
    fun x hx μ hμ => ?_⟩
  show weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ x = 0
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd h
  apply hμ
  rw [Finset.mem_image]
  refine ⟨d, ?_, h⟩
  rw [Set.Finite.mem_toFinset]
  exact (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hx hd

theorem wt_sub_le (LL L2 : Letters N) (j : ℕ) (c : Fin r) {m m' : Fin N × Fin r →₀ ℕ}
    (hm : MultiDeg L2 m) (hm' : MultiDeg L2 m') : wt LL j c m' - wt LL j c m ≤ (L2.total : ℤ) := by
  unfold wt Letters.total
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : m (i, c) ≤ L2.deg i := by
    rw [← hm i]
    exact Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have h2 : m' (i, c) ≤ L2.deg i := by
    rw [← hm' i]
    exact Finset.single_le_sum (f := fun c => m' (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  split_ifs <;> omega

theorem GAe_pol_bound (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    ∀ (μ ν : Fin n → ℤ) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ Pol p r L2 → y ∈ Pol p r L2 → (GAe p LL j e).IsWt μ x → (GAe p LL j e).IsWt ν y →
      ∀ c, |ν c - μ c| ≤ (L2.total : ℤ) := by
  intro μ ν x y hx0 hy0 hx hy hμ hν c
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff] at hμ hν
  obtain ⟨m, hm⟩ := (MvPolynomial.support_nonempty).mpr hx0
  obtain ⟨m', hm'⟩ := (MvPolynomial.support_nonempty).mpr hy0
  have d1 : MultiDeg L2 m := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hx hm
  have d2 : MultiDeg L2 m' := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hy hm'
  rw [← hμ hm c, ← hν hm' c, abs_le]
  have a1 := wt_sub_le LL L2 j (e c) d1 d2
  have a2 := wt_sub_le LL L2 j (e c) d2 d1
  constructor <;> linarith

theorem monomial_mem_pol (LL : Letters N) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    monomial m a ∈ Pol p r (⟨LL.vec, fun i => ∑ c, m (i, c)⟩ : Letters N) := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  have := MvPolynomial.support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  intro i
  rfl

end Formalism.InvariantFactorPaths.PW
