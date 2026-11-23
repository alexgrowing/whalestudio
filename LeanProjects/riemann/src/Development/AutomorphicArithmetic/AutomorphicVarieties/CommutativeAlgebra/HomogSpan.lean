import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add, h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add, h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

theorem UpperTheory.V.Alg.homog_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] (W : WPres O X R) (κ : Type) [Finite κ] (g : κ → W.A) (c : κ → X), (∀ i, g i ∈ W.gr (c i)) →
      IsHomog O W.wt ((Ideal.span (Set.range fun i => (g i : R))).comap W.π) ∧
      ∀ x : W.A, (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) ↔ x ∈ Ideal.span (Set.range g) := by
  intro O R _ _ _ X _ W κ _ g c hg
  classical
  cases nonempty_fintype κ
  have hback : ∀ x : W.A, x ∈ Ideal.span (Set.range g) →
      (x : R) ∈ Ideal.span (Set.range fun i => (g i : R)) := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => (a i : R), ?_⟩
    rw [← ha]
    simp
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = (g i : R) := fun i => hg i
  choose e he heg using hg'
  have key : ∀ f, W.π f ∈ Ideal.span (Set.range fun i => (g i : R)) → ∀ j,
      ∃ y ∈ Ideal.span (Set.range g), (y : R) = W.π (wcomp O W.wt j f) := by
    intro f hf j
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
    choose G hG using fun i => W.surj (a i)
    have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, ← ha, map_sum]
      simp [hG, heg]
    have h2 := W.homog _ h1 j
    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    have hm : ∀ i, W.π (wcomp O W.wt (j - c i) (G i)) ∈ W.A := fun i =>
      W.part_le_A (j := j - c i) ⟨_, wcomp_mem O W.wt _ _, rfl⟩
    refine ⟨∑ i, ⟨_, hm i⟩ * g i, Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨_, hm i⟩, rfl⟩, ?_⟩
    rw [h2, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
    rfl
  refine ⟨fun f hf j => ?_, fun x => ⟨fun hx => ?_, hback x⟩⟩
  · obtain ⟨y, hy, hy'⟩ := key f hf j
    rw [Ideal.mem_comap, ← hy']
    exact hback y hy
  · have hx' : (x : R) ∈ ⨆ j, W.part j := x.2
    have hl : ∃ f, W.π f = (x : R) ∧ ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
      refine Submodule.iSup_induction W.part
        (motive := fun z : R => ∃ f, W.π f = z ∧
          ∃ s : Finset X, ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
      · rintro i _ ⟨f, hf, rfl⟩
        exact ⟨f, rfl, {i}, fun n hn => hf n (by simpa using hn)⟩
      · exact ⟨0, map_zero _, ∅, fun n _ => map_zero _⟩
      · rintro a b ⟨f, hf, s, hs⟩ ⟨f', hf', s', hs'⟩
        refine ⟨f + f', by rw [map_add, hf, hf'], s ∪ s', fun n hn => ?_⟩
        rw [Finset.mem_union, not_or] at hn
        rw [map_add, hs n hn.1, hs' n hn.2, add_zero]
    obtain ⟨f, hf, s, hs⟩ := hl
    have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
      ext n
      rw [map_sum]
      simp only [coeff_wcomp]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hs n h
    choose y hy hy' using key f (hf ▸ hx)
    have : x = ∑ j ∈ s, y j := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum, ← hf]
      conv_lhs => rw [hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hy' j).symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => hy j
