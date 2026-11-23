import Mathlib

theorem UpperTheory.Reformulated.B.IntegralSumCosets.integral_eq_measure_mul_sum_cosets :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulRightInvariant] [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
          (∀ (a b : ι), R a * (R b)⁻¹ ∈ K → a = b) →
            (∀ κ ∈ K, ∀ (g : G), f (κ * g) = f g) →
              (∀ (g : G), f g ≠ (0 : ℂ) → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
                ∫ (g : G), f g ∂μ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
  intro G _ _ _ _ _ μ _ _ K hKo hKc ι R S f hR hf hsupp
  classical
  have hmeas : ∀ a : ι, MeasurableSet ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) := fun a =>
    (hKo.preimage (continuous_id.mul continuous_const)).measurableSet
  have hμ : ∀ a : ι, μ ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) = μ (K : Set G) := fun a =>
    MeasureTheory.measure_preimage_mul_right μ _ _
  have hval : ∀ (a : ι) (g : G), g * (R a)⁻¹ ∈ K → f g = f (R a) := by
    intro a g hg
    have h := hf _ hg (R a)
    rwa [inv_mul_cancel_right] at h
  have hdec : f = fun g => ∑ a ∈ S,
      ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g := by
    funext g
    by_cases hex : ∃ a ∈ S, g * (R a)⁻¹ ∈ K
    · obtain ⟨a, haS, ha⟩ := hex
      rw [Finset.sum_eq_single a]
      · rw [Set.indicator_of_mem (by exact ha)]
        exact hval a g ha
      · intro b _ hba
        apply Set.indicator_of_notMem
        intro hb
        apply hba
        apply hR
        have hb' : g * (R b)⁻¹ ∈ K := hb
        have h := K.mul_mem (K.inv_mem hb') ha
        have e : (g * (R b)⁻¹)⁻¹ * (g * (R a)⁻¹) = R b * (R a)⁻¹ := by group
        rwa [e] at h
      · intro h
        exact absurd haS h
    · have h0 : f g = 0 := by
        by_contra h
        exact hex (hsupp g h)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro a haS
      apply Set.indicator_of_notMem
      intro ha
      exact hex ⟨a, haS, ha⟩
  have hint : ∀ a ∈ S, MeasureTheory.Integrable
      (((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a))) μ := by
    intro a _
    rw [MeasureTheory.integrable_indicator_iff (hmeas a)]
    exact MeasureTheory.integrableOn_const (by rw [hμ a]; exact hKc.measure_lt_top.ne)
  calc ∫ g, f g ∂μ
      = ∫ g, ∑ a ∈ S,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        congrArg (fun F : G → ℂ => ∫ g, F g ∂μ) hdec
    _ = ∑ a ∈ S, ∫ g,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        MeasureTheory.integral_finset_sum S hint
    _ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_indicator_const _ (hmeas a), MeasureTheory.measureReal_def,
          hμ a, MeasureTheory.measureReal_def, Complex.real_smul]
