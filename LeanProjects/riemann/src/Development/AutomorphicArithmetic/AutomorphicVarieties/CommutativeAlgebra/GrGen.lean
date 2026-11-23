import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_fin_min {σ : Type} [Fintype σ] (P : (σ →₀ ℕ) → Prop) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m ∈ T, P m) ∧ ∀ n, P n → ∃ m ∈ T, m ≤ n := by
  classical
  have hfin : {m : σ →₀ ℕ | Minimal P m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, ?_⟩
  intro n hn
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | P x}).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

private theorem exists_decomp {O σ X : Type} [CommRing O] [Fintype σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) :
    ∃ (T : Finset (σ →₀ ℕ)) (g : (σ →₀ ℕ) → MvPowerSeries σ O), (∀ m ∈ T, g m ∈ wtPart O wt 0) ∧
      f = ∑ m ∈ T, monomial m (1 : O) * g m := by
  classical
  obtain ⟨T, hTP, hT⟩ := exists_fin_min (fun n => coeff n f ≠ 0)
  choose! c hcT hcle using hT
  obtain ⟨g, hg⟩ : ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, ∀ m k,
      coeff k (g m) = if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0 :=
    ⟨fun m k => if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
  have hwt : ∀ n, coeff n f ≠ 0 → Finsupp.weight wt n = j := by
    intro n hn
    by_contra h
    exact hn (hf n h)
  refine ⟨T, g, ?_, ?_⟩
  · intro m hmT k hk
    rw [hg, if_neg]
    rintro ⟨h1, h2⟩
    apply hk
    have hm : Finsupp.weight wt m = j := hwt m (hTP m hmT)
    have hkm := hwt _ h1
    rw [map_add, hm] at hkm
    simpa using hkm
  · ext n
    rw [map_sum, Finset.sum_congr rfl
      (g := fun m => if c n = m then (if coeff n f ≠ 0 then coeff n f else 0) else 0),
      Finset.sum_ite_eq]
    · by_cases hn : coeff n f ≠ 0
      · rw [if_pos (hcT n hn), if_pos hn]
      · push_neg at hn
        rw [hn]
        simp
    · intro m _
      rw [MvPowerSeries.coeff_monomial_mul, one_mul]
      by_cases hmn : m ≤ n
      · rw [if_pos hmn, hg, tsub_add_cancel_of_le hmn]
        by_cases h1 : coeff n f ≠ 0 <;> by_cases h2 : c n = m <;> simp [h1, h2]
      · rw [if_neg hmn]
        by_cases h1 : coeff n f ≠ 0
        · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
          simp [h3]
        · push_neg at h1
          simp [h1]

private theorem monomial_eq_prod {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  have key : ∀ s : Finset σ, ∏ i ∈ s, (MvPowerSeries.X i : MvPowerSeries σ O) ^ (m i) =
      monomial (∑ i ∈ s, Finsupp.single i (m i)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MvPowerSeries.monomial_zero_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

theorem UpperTheory.V.Alg.gr_gen :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R), Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) = ⊤ := by
  intro O R _ _ _ X _ _ _ W
  classical
  haveI := W.fin
  rw [Algebra.eq_top_iff]
  rintro ⟨x, hx⟩
  refine Submodule.iSup_induction' (p := W.part)
    (motive := fun x h => (⟨x, h⟩ : W.A) ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA))
    ?_ ?_ ?_ hx
  · intro j y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨T, g, hg, hfe⟩ := exists_decomp W.wt j f hf
    have hg' : ∀ m, (if m ∈ T then g m else 0) ∈ wtPart O W.wt 0 := by
      intro m
      split_ifs with h
      · exact hg m h
      · exact zero_mem _
    let e : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (if m ∈ T then g m else 0), W.part_le_A (Submodule.mem_map_of_mem (hg' m))⟩
    have he : ∀ m, e m ∈ W.gr 0 := fun m => Submodule.mem_map_of_mem (hg' m)
    have hmem : (∑ m ∈ T, (∏ i, W.zA i ^ m i) * e m) ∈
        Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
      · refine Subalgebra.prod_mem _ fun i _ => pow_mem ?_ _
        exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (he m))
    convert hmem using 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_finset_prod,
      SubmonoidClass.coe_pow, e, WPres.zA, WPres.z]
    rw [AlgHom.toLinearMap_apply, hfe, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm, map_mul, monomial_eq_prod, map_prod]
    simp only [map_pow]
  · exact Subalgebra.zero_mem _
  · intro x y _ _ ihx ihy
    exact Subalgebra.add_mem _ ihx ihy
