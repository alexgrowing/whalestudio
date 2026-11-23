import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

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

private theorem span_coeffs {O R X κ N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    (W : WPres O X R) [Fintype κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i)) (u : N → X)
    (B : Submodule O R) (hB : ∀ n i, W.part (u n - c i) ≤ B) (x : R) (hx' : x ∈ ⨆ n, W.part (u n))
    (hx : x ∈ Ideal.span (Set.range g)) : ∃ a : κ → R, (∀ i, a i ∈ B) ∧ x = ∑ i, a i * g i := by
  classical
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = g i := fun i => hg i
  choose e he heg using hg'
  have hl : ∃ f, W.π f = x ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
      ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
    refine Submodule.iSup_induction (fun n => W.part (u n))
      (motive := fun z : R => ∃ f, W.π f = z ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
        ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
    · rintro i _ ⟨f, hf, rfl⟩
      exact ⟨f, rfl, {u i}, fun j hj => ⟨i, (Finset.mem_singleton.1 hj).symm⟩,
        fun n hn => hf n (by simpa using hn)⟩
    · exact ⟨0, map_zero _, ∅, by simp, fun n _ => map_zero _⟩
    · rintro a b ⟨f, hf, s, ht, hs⟩ ⟨f', hf', s', ht', hs'⟩
      refine ⟨f + f', by rw [map_add, hf, hf'], s ∪ s', fun j hj => ?_, fun n hn => ?_⟩
      · rcases Finset.mem_union.1 hj with h | h
        · exact ht j h
        · exact ht' j h
      · rw [Finset.mem_union, not_or] at hn
        rw [map_add, hs n hn.1, hs' n hn.2, add_zero]
  obtain ⟨f, hf, s, ht, hs⟩ := hl
  have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
    ext n
    rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hs n h
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose G hG using fun i => W.surj (a i)
  have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
    rw [RingHom.mem_ker, map_sub, hf, ← ha, map_sum]
    simp [hG, heg]
  have key : ∀ j, W.π (wcomp O W.wt j f) = ∑ i, W.π (wcomp O W.wt (j - c i) (G i)) * g i := by
    intro j
    have h2 := W.homog _ h1 j
    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
  refine ⟨fun i => ∑ j ∈ s, W.π (wcomp O W.wt (j - c i) (G i)), fun i => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => ?_
    obtain ⟨n, rfl⟩ := ht j hj
    exact hB n i ⟨_, wcomp_mem O W.wt _ _, rfl⟩
  · rw [← hf]
    conv_lhs => rw [hsum]
    rw [map_sum]
    simp only [key, Finset.sum_mul]
    exact Finset.sum_comm

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.kerA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, (∀ f : M.A, M.toSS f = 0 ↔ f ∈ M.eqns.ideal) ∧ (∀ n (x : M.SS), x.1 ∈ M.sPart (0, n) → ∃ f ∈ M.gr n, M.toSS f = x) ∧ ∀ n, ∀ f ∈ M.gr n, (M.toSS f).1 ∈ M.sPart (0, n) := by
  intro Ω _ _ _ l _ c D _ M
  refine ⟨fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_, ?_⟩
  · have h0 : (f : M.R) ∈ RingHom.ker M.π := congrArg Subtype.val hf
    rw [M.ker, ← Set.Sum.elim_range, ← Set.Sum.elim_range] at h0
    obtain ⟨a, ha, hfa⟩ := span_coeffs M.W (Sum.elim (Sum.elim M.F M.E) M.Z)
      (fun i => ((0 : ℤ), Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i))
      (by
        rintro ((i | i) | i)
        · exact M.hF i
        · exact M.hE i
        · exact (M.hZ i).1)
      (fun n : ℤ => ((0 : ℤ), n)) (Subalgebra.toSubmodule M.A)
      (fun n i x hx => M.aPart_le (n := n - Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i)
        (by simpa [Model.aPart] using hx))
      f f.2 h0
    have hf' : f = ∑ i, (⟨a i, ha i⟩ : M.A) * Sum.elim (Sum.elim M.eqns.F M.eqns.E) M.eqns.Z i := by
      apply Subtype.ext
      rw [hfa, AddSubmonoidClass.coe_finset_sum]
      refine Finset.sum_congr rfl ?_
      rintro ((i | i) | i) - <;> rfl
    rw [hf']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    rcases i with (i | i) | i
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Or.inr ⟨i, rfl⟩
  · have hle : M.eqns.ideal ≤ RingHom.ker M.toSS := by
      refine Ideal.span_le.2 fun x hx => ?_
      have hk : (x : M.R) ∈ RingHom.ker M.π := by
        rw [M.ker]
        refine Ideal.subset_span ?_
        rcases hx with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact Or.inl (Or.inl ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inl (Or.inr ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inr ⟨i, rfl⟩
      exact Subtype.ext hk
    exact hle hf
  · rintro n x ⟨f, hf, hfx⟩
    exact ⟨⟨f, M.aPart_le (n := n) hf⟩, hf, Subtype.ext hfx⟩
  · intro n f hf
    exact ⟨f, hf, rfl⟩
