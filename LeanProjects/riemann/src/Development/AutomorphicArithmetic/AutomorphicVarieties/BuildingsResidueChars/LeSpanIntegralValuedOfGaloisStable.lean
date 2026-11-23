import Mathlib

private theorem UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    [Algebra.IsAlgebraic O ℂ] (z : ℂ) (hz : ∀ γ : ℂ ≃ₐ[O] ℂ, γ z = z) :
    ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * z = algebraMap O ℂ a := by
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  haveI : Algebra.IsAlgebraic (FractionRing O) ℂ :=
    Algebra.IsAlgebraic.extendScalars (FaithfulSMul.algebraMap_injective O (FractionRing O))
  haveI : CharZero (FractionRing O) := RingHom.charZero (algebraMap (FractionRing O) ℂ)
  haveI : Algebra.IsSeparable (FractionRing O) ℂ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure (FractionRing O) ℂ := ⟨inferInstance, inferInstance⟩
  haveI : Normal (FractionRing O) ℂ := inferInstance
  haveI : IsGalois (FractionRing O) ℂ := ⟨⟩
  have hmem : z ∈ Set.range (algebraMap (FractionRing O) ℂ) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed z).2 (fun f => hz (f.restrictScalars O))
  obtain ⟨q, rfl⟩ := hmem
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) q
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  show algebraMap O ℂ b * algebraMap (FractionRing O) ℂ (IsLocalization.mk' (FractionRing O) a b) =
    algebraMap O ℂ a
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ (b : O),
    IsScalarTower.algebraMap_apply O (FractionRing O) ℂ a, ← map_mul, mul_comm,
    IsLocalization.mk'_spec]

theorem UpperTheory.le_span_integralValued_of_galoisStable :
    ∀ (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (X : Type) [Finite X] (I : Submodule ℂ (X → ℂ)), (∀ γ : ℂ ≃ₐ[O] ℂ, ∀ x ∈ I, (fun g => γ (x g)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
  intro O _ _ _ _ _ X _ I hI
  classical
  haveI := Fintype.ofFinite X
  have hfix : ∀ x ∈ I, (∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x) →
      x ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro x hx hγ
    have hc : ∀ g, ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * x g = algebraMap O ℂ a :=
      fun g => UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed O (x g) (fun γ => congrFun (hγ γ) g)
    choose a b hb hab using hc
    have hB : algebraMap O ℂ (∏ g, b g) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun g _ =>
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O ℂ)).2 (hb g))
    have hmem : algebraMap O ℂ (∏ g, b g) • x ∈
        Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
      apply Submodule.subset_span
      refine ⟨I.smul_mem _ hx, fun g => ⟨a g * ∏ h ∈ Finset.univ.erase g, b h, ?_⟩⟩
      show algebraMap O ℂ (a g * ∏ h ∈ Finset.univ.erase g, b h) = algebraMap O ℂ (∏ g, b g) * x g
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ g)]
      simp only [map_mul, ← hab g]
      ring
    have h2 := Submodule.smul_mem _ (algebraMap O ℂ (∏ g, b g))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hB, one_smul] at h2
  have key : ∀ n : ℕ, ∀ y ∈ I, (Finset.univ.filter (fun g => y g ≠ 0)).card ≤ n →
      y ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro n
    induction n with
    | zero =>
      intro y hy hc
      have hy0 : y = 0 := by
        funext g
        by_contra h
        have := Finset.card_pos.2
          ⟨g, (by simpa using h : g ∈ Finset.univ.filter (fun g => y g ≠ 0))⟩
        omega
      rw [hy0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro y hy hc
      by_cases h0 : y = 0
      · rw [h0]
        exact Submodule.zero_mem _
      obtain ⟨g0, hg0⟩ : ∃ g, y g ≠ 0 := by
        by_contra h
        push_neg at h
        exact h0 (funext h)
      obtain ⟨x, hx⟩ : ∃ x : X → ℂ, x = (y g0)⁻¹ • y := ⟨_, rfl⟩
      have hxI : x ∈ I := by
        rw [hx]
        exact I.smul_mem _ hy
      have hxg0 : x g0 = 1 := by
        rw [hx]
        simp [hg0]
      have hsupp : ∀ g, x g = 0 ↔ y g = 0 := by
        intro g
        rw [hx]
        simp [hg0]
      have hyx : y = y g0 • x := by
        rw [hx, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      by_cases hall : ∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x
      · rw [hyx]
        exact Submodule.smul_mem _ _ (hfix x hxI hall)
      · push_neg at hall
        obtain ⟨γ, hγ⟩ := hall
        obtain ⟨d, hd⟩ : ∃ d : X → ℂ, d = (fun g => γ (x g)) - x := ⟨_, rfl⟩
        have hdI : d ∈ I := by
          rw [hd]
          exact I.sub_mem (hI γ x hxI) hxI
        have hd0 : d ≠ 0 := by
          rw [hd]
          exact sub_ne_zero.2 hγ
        obtain ⟨g1, hg1⟩ : ∃ g, d g ≠ 0 := by
          by_contra h
          push_neg at h
          exact hd0 (funext h)
        have hdsupp : ∀ g, y g = 0 → d g = 0 := by
          intro g hg
          rw [hd]
          simp [(hsupp g).2 hg]
        have hdg0 : d g0 = 0 := by
          rw [hd]
          simp [hxg0]
        have hy1 : y g1 ≠ 0 := fun e => hg1 (hdsupp g1 e)
        have hdcard : (Finset.univ.filter (fun g => d g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => d g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g0 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun e => hg (e ▸ hdg0), fun e => hg (hdsupp g e)⟩
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g0 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hg0])
          omega
        have hdW := ih d hdI hdcard
        obtain ⟨y', hy'⟩ : ∃ y' : X → ℂ, y' = y - (y g1 / d g1) • d := ⟨_, rfl⟩
        have hy'I : y' ∈ I := by
          rw [hy']
          exact I.sub_mem hy (I.smul_mem _ hdI)
        have hy'card : (Finset.univ.filter (fun g => y' g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => y' g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g1 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · rintro rfl
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hg1, sub_self]
            · intro e
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e, hdsupp g e, mul_zero, sub_zero]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g1 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hy1])
          omega
        have hy'W := ih y' hy'I hy'card
        have hyy : y = y' + (y g1 / d g1) • d := by
          rw [hy', sub_add_cancel]
        rw [hyy]
        exact Submodule.add_mem _ hy'W (Submodule.smul_mem _ _ hdW)
  intro y hy
  exact key _ y hy le_rfl
