import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

private theorem erase_eq_and_apply_eq_iff_eq_add_single {ι : Type} (i : ι) (k : ℕ) (s u : ι →₀ ℕ) (hu : u i = 0) :
    (s.erase i = u ∧ s i = k) ↔ s = u + Finsupp.single i k := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu, h2]
    · have h3 : (s.erase i) j = u j := by rw [h1]
      rw [Finsupp.erase_ne hj] at h3
      simp [Ne.symm hj, h3]
  · rintro rfl
    refine ⟨?_, by simp [hu]⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu]
    · simp [Finsupp.erase_ne hj]

theorem coeff_coeffIn {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) (u : ι →₀ ℕ) :
    (coeffIn i k f).coeff u = if u i = 0 then f.coeff (u + Finsupp.single i k) else 0 := by
  classical
  unfold coeffIn
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with hu
  · have hsp := (erase_eq_and_apply_eq_iff_eq_add_single i k (u + Finsupp.single i k) u hu).mpr rfl
    rw [Finset.sum_eq_single (u + Finsupp.single i k)]
    · rw [if_pos hsp.1]
    · intro t ht hne
      rw [if_neg]
      intro hte
      exact hne ((erase_eq_and_apply_eq_iff_eq_add_single i k t u hu).mp ⟨hte, (Finset.mem_filter.mp ht).2⟩)
    · intro hnot
      rw [if_pos hsp.1]
      by_contra hc
      exact hnot (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hc, hsp.2⟩)
  · apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    rintro rfl
    exact hu (by simp)

private theorem apply_eq_zero_and_add_single_mem_support_of_coeffIn {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ)
    (u : ι →₀ ℕ) (hu : u ∈ (coeffIn i k f).support) :
    u i = 0 ∧ u + Finsupp.single i k ∈ f.support := by
  rw [MvPolynomial.mem_support_iff, coeff_coeffIn] at hu
  by_cases h : u i = 0
  · rw [if_pos h] at hu
    exact ⟨h, MvPolynomial.mem_support_iff.mpr hu⟩
  · rw [if_neg h] at hu
    exact absurd rfl hu

private theorem eq_monomial_of_vars_eq_empty {ι : Type} [LinearOrder ι] (g : MvPolynomial ι ℂ)
    (s : ι →₀ ℕ) (hmin : ∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i)
    (hv : g.vars = ∅) : g = MvPolynomial.monomial s (g.coeff s) := by
  classical
  ext u
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · by_contra hc
    obtain ⟨i, -, hi⟩ := hmin u (MvPolynomial.mem_support_iff.mpr hc) (Ne.symm h)
    have hmem : i ∈ g.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr
      ⟨u, MvPolynomial.mem_support_iff.mpr hc,
        Finsupp.mem_support_iff.mpr ((Nat.zero_le _).trans_lt hi).ne'⟩
    rw [hv] at hmem
    simp at hmem

theorem torusLex_of (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement := by
  unfold ReciprocityTheory.MultiplicativeHeights.TorusLexStatement
  intro ι _ _ f s hs hmin
  have base : ∀ (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ),
      (∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) → g.vars = ∅ →
      Real.log ‖g.coeff s‖ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g := by
    intro g s hmin hv
    have hg := eq_monomial_of_vars_eq_empty g s hmin hv
    have h1 : ReciprocityTheory.MultiplicativeHeights.torusMean g = Real.log ‖g.coeff s‖ :=
      (congrArg ReciprocityTheory.MultiplicativeHeights.torusMean hg).trans ((hBasic ι).2.2 s _)
    exact h1.ge
  suffices key : ∀ n : ℕ, ∀ (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ), g.vars.card ≤ n →
      s ∈ g.support → (∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) →
      Real.log ‖g.coeff s‖ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g from key _ f s le_rfl hs hmin
  intro n
  induction n with
  | zero =>
    intro g s hcard _ hmin
    exact base g s hmin (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro g s hcard hs hmin
    by_cases hv : g.vars = ∅
    · exact base g s hmin hv
    have hne : g.vars.Nonempty := Finset.nonempty_iff_ne_empty.mpr hv
    obtain ⟨i, hiv, himin⟩ : ∃ i ∈ g.vars, ∀ j ∈ g.vars, i ≤ j :=
      ⟨g.vars.min' hne, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj⟩
    have hlow : ∀ t ∈ g.support, s i ≤ t i := by
      intro t ht
      by_cases hts : t = s
      · rw [hts]
      · obtain ⟨i', hpre, hlt⟩ := hmin t ht hts
        have hi'v : i' ∈ g.vars := (MvPolynomial.mem_vars_iff_mem_support i').mpr
          ⟨t, ht, Finsupp.mem_support_iff.mpr ((Nat.zero_le _).trans_lt hlt).ne'⟩
        rcases (himin i' hi'v).lt_or_eq with h | h
        · exact (hpre i h).le
        · rw [h]
          exact hlt.le
    have h0 : (s.erase i) i = 0 := by simp
    have hsplit : s = s.erase i + Finsupp.single i (s i) :=
      (erase_eq_and_apply_eq_iff_eq_add_single i (s i) s (s.erase i) h0).mp ⟨rfl, rfl⟩
    have hcoef : (coeffIn i (s i) g).coeff (s.erase i) = g.coeff s := by
      rw [coeff_coeffIn, if_pos h0, ← hsplit]
    have hne' : coeffIn i (s i) g ≠ 0 := by
      intro hz
      have h2 := hcoef
      rw [hz, MvPolynomial.coeff_zero] at h2
      exact (MvPolynomial.mem_support_iff.mp hs) h2.symm
    have hs' : s.erase i ∈ (coeffIn i (s i) g).support := by
      rw [MvPolynomial.mem_support_iff, hcoef]
      exact MvPolynomial.mem_support_iff.mp hs
    have hvan : ∀ k', k' < s i → coeffIn i k' g = 0 := by
      intro k' hk'
      unfold coeffIn
      apply Finset.sum_eq_zero
      intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
      exact absurd (hlow t ht1) (by omega)
    have hmin' : ∀ t' ∈ (coeffIn i (s i) g).support, t' ≠ s.erase i →
        ∃ j, (∀ l < j, (s.erase i) l = t' l) ∧ (s.erase i) j < t' j := by
      intro t' ht' hne2
      obtain ⟨ht0, ht⟩ := apply_eq_zero_and_add_single_mem_support_of_coeffIn i (s i) g t' ht'
      have hsp := (erase_eq_and_apply_eq_iff_eq_add_single i (s i) (t' + Finsupp.single i (s i)) t' ht0).mpr rfl
      have hts : t' + Finsupp.single i (s i) ≠ s := by
        intro h
        apply hne2
        rw [← hsp.1, h]
      obtain ⟨j, hpre, hlt⟩ := hmin _ ht hts
      have hji : j ≠ i := by
        rintro rfl
        rw [hsp.2] at hlt
        exact lt_irrefl _ hlt
      refine ⟨j, fun l hl => ?_, ?_⟩
      · rw [← hsp.1]
        by_cases hli : l = i
        · simp [hli]
        · rw [Finsupp.erase_ne hli, Finsupp.erase_ne hli]
          exact hpre l hl
      · rw [← hsp.1, Finsupp.erase_ne hji, Finsupp.erase_ne hji]
        exact hlt
    have hvars : (coeffIn i (s i) g).vars ⊆ g.vars.erase i := by
      intro j hj
      obtain ⟨t', ht', hjt⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
      obtain ⟨ht0, ht⟩ := apply_eq_zero_and_add_single_mem_support_of_coeffIn i (s i) g t' ht'
      have hji : j ≠ i := by
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hjt) ht0
      refine Finset.mem_erase.mpr ⟨hji, (MvPolynomial.mem_vars_iff_mem_support j).mpr ⟨_, ht, ?_⟩⟩
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hji),
        add_zero]
      exact Finsupp.mem_support_iff.mp hjt
    have hcard' : (coeffIn i (s i) g).vars.card ≤ n := by
      have h1 := Finset.card_le_card hvars
      rw [Finset.card_erase_of_mem hiv] at h1
      omega
    calc Real.log ‖g.coeff s‖ = Real.log ‖(coeffIn i (s i) g).coeff (s.erase i)‖ := by rw [hcoef]
      _ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean (coeffIn i (s i) g) := ih _ _ hcard' hs' hmin'
      _ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g := hCoeff ι g i (s i) hne' (Or.inr hvan)

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
