import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

private theorem comp_C_mul_X_ne_zero_and_rootMultiplicity {P : Polynomial ℂ} (hP : P ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    P.comp (Polynomial.C r * Polynomial.X) ≠ 0 ∧
      ∀ z, (P.comp (Polynomial.C r * Polynomial.X)).rootMultiplicity z = P.rootMultiplicity (r * z) := by
  refine ⟨fun h0 => hP ((Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hr)).mp h0),
    fun z => ?_⟩
  have := Polynomial.rootMultiplicity_comp_C_mul_X_add_C P r 0 z (isUnit_iff_ne_zero.mpr hr)
  simpa using this

open Polynomial in
theorem UpperTheory.V.Z.Gam.secDiff :
    UpperTheory.V.Z.Gam.SecDiff := by
  classical
  intro q hq P P' c hP hP' h
  have hqpos : (0 : ℝ) < q := by linarith
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hqi : ((q : ℂ))⁻¹ ≠ 0 := inv_ne_zero hq0
  have hc : c = 1 := by
    have h0 := congrArg (Polynomial.eval 0) h
    simp [Polynomial.eval_comp, hP, hP'] at h0
    first
      | exact h0.symm
      | exact h0
  subst hc
  have hPne : P ≠ 0 := by
    rintro rfl
    simp at hP
  have hP'ne : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  obtain ⟨hA, mA⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hqi
  obtain ⟨hB, mB⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hq0
  obtain ⟨hA', mA'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hqi
  obtain ⟨hB', mB'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hq0
  rw [map_one, one_mul] at h
  have key : ∀ z : ℂ, P.rootMultiplicity ((q : ℂ)⁻¹ * z) + P.rootMultiplicity ((q : ℂ) * z) +
      (P'.rootMultiplicity z + P'.rootMultiplicity z) =
      P'.rootMultiplicity ((q : ℂ)⁻¹ * z) + P'.rootMultiplicity ((q : ℂ) * z) +
      (P.rootMultiplicity z + P.rootMultiplicity z) := by
    intro z
    have hz := congrArg (Polynomial.rootMultiplicity z) h
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hP'ne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hPne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA hB),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA' hB'), sq, sq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hP'ne hP'ne),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hPne hPne), mA, mB, mA', mB'] at hz
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℤ, ∀ z, d z = (P.rootMultiplicity z : ℤ) - P'.rootMultiplicity z :=
    ⟨_, fun z => rfl⟩
  have rel : ∀ z, d ((q : ℂ)⁻¹ * z) + d ((q : ℂ) * z) = 2 * d z := by
    intro z
    have := key z
    simp only [hd]
    omega
  have p0 : P.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP] at this)
  have p0' : P'.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP'] at this)
  have d0 : d 0 = 0 := by simp [hd, p0, p0']
  have supp : ∀ z, d z ≠ 0 → z ∈ (P * P').roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (mul_ne_zero hPne hP'ne)]
    change Polynomial.eval z (P * P') = 0
    rw [Polynomial.eval_mul]
    by_contra hne
    apply hz
    have r1 : P.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, zero_mul]))
    have r2 : P'.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, mul_zero]))
    simp [hd, r1, r2]
  have hdz : ∀ z, d z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨z1, hz1⟩ := hne
    set S := (P * P').roots.toFinset.filter (fun z => d z ≠ 0) with hS
    have hSne : S.Nonempty := ⟨z1, Finset.mem_filter.mpr ⟨supp z1 hz1, hz1⟩⟩
    obtain ⟨z0, hz0S, hmax⟩ := S.exists_max_image (fun z => ‖z‖) hSne
    have hz0 : d z0 ≠ 0 := (Finset.mem_filter.mp hz0S).2
    have hz00 : z0 ≠ 0 := by
      rintro rfl
      exact hz0 d0
    have hnz0 : 0 < ‖z0‖ := norm_pos_iff.mpr hz00
    have hnorm : ∀ k : ℕ, ‖(q : ℂ)⁻¹ ^ k * z0‖ = q⁻¹ ^ k * ‖z0‖ := by
      intro k
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    have hup : d ((q : ℂ) * z0) = 0 := by
      by_contra hne2
      have hm := hmax _ (Finset.mem_filter.mpr ⟨supp _ hne2, hne2⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos] at hm
      nlinarith
    have step : ∀ k : ℕ, d ((q : ℂ)⁻¹ ^ k * z0) = (k + 1) * d z0 ∧
        d ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (k + 2) * d z0 := by
      intro k
      induction k with
      | zero =>
        have r0 := rel z0
        rw [hup] at r0
        refine ⟨by simp, ?_⟩
        simp only [zero_add, pow_one, Nat.cast_zero]
        linarith
      | succ k ih =>
        refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
        have r1 := rel ((q : ℂ)⁻¹ ^ (k + 1) * z0)
        have e1 : (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ (k + 1 + 1) * z0 := by ring
        have e2 : (q : ℂ) * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ k * z0 := by
          rw [pow_succ]
          linear_combination ((q : ℂ)⁻¹ ^ k * z0) * mul_inv_cancel₀ hq0
        rw [e1, e2, ih.1, ih.2] at r1
        push_cast
        linear_combination r1
    have hmem : ∀ k : ℕ, (q : ℂ)⁻¹ ^ k * z0 ∈ (S : Set ℂ) := by
      intro k
      have hk : d ((q : ℂ)⁻¹ ^ k * z0) ≠ 0 := by
        rw [(step k).1]
        exact mul_ne_zero (by positivity) hz0
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨supp _ hk, hk⟩)
    have hinj : Function.Injective (fun k : ℕ => (q : ℂ)⁻¹ ^ k * z0) := by
      intro a b hab
      have hn := congrArg norm hab
      simp only [hnorm] at hn
      have hab' := mul_right_cancel₀ hnz0.ne' hn
      refine pow_right_injective₀ (inv_pos.mpr hqpos) ?_ hab'
      intro h1
      simp at h1
      linarith
    exact Set.infinite_of_injective_forall_mem hinj hmem S.finite_toSet
  have hm : ∀ z, P.rootMultiplicity z = P'.rootMultiplicity z := by
    intro z
    have := hdz z
    rw [hd] at this
    omega
  have hroots : P.roots = P'.roots := by
    ext z
    rw [Polynomial.count_roots, Polynomial.count_roots, hm]
  have e1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
    IsAlgClosed.card_roots_eq_natDegree
  have e2 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P')
    IsAlgClosed.card_roots_eq_natDegree
  rw [hroots] at e1
  have v1 := congrArg (Polynomial.eval 0) e1
  have v2 := congrArg (Polynomial.eval 0) e2
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP] at v1
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP'] at v2
  have hlc : P.leadingCoeff = P'.leadingCoeff := by
    have hne : Polynomial.eval 0
        (Multiset.map (fun a => Polynomial.X - Polynomial.C a) P'.roots).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at v2
      exact zero_ne_one v2
    exact mul_right_cancel₀ hne (v1.trans v2.symm)
  rw [hlc] at e1
  exact e1.symm.trans e2
