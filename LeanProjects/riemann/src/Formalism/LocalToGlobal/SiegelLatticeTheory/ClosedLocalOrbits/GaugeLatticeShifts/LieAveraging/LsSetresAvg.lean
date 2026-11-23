import Mathlib

noncomputable section

open MeasureTheory Topology Set
open scoped Pointwise ENNReal

namespace Formalism.L2.SG.AvgPf

theorem isFD_of_strict {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] (μ : Measure α) {S : Set α}
    (hS : MeasurableSet S) (hcov : ∀ᵐ x ∂μ, ∃ g : Γ, g • x ∈ S)
    (huniq : ∀ x ∈ S, ∀ g : Γ, g • x ∈ S → g = 1) : IsFundamentalDomain Γ S μ := by
  refine ⟨hS.nullMeasurableSet, hcov, ?_⟩
  intro g h hgh
  show AEDisjoint μ (g • S) (h • S)
  refine Disjoint.aedisjoint ?_
  rw [Set.disjoint_left]
  rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hmem : (h⁻¹ * g) • a ∈ S := by
    have hba' : h • b = g • a := hba
    rw [mul_smul, ← hba', inv_smul_smul]
    exact hb
  have e := huniq a ha _ hmem
  rw [inv_mul_eq_one] at e
  exact hgh e.symm

theorem fd_ne_zero {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : Measure α}
    [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Countable Γ] {S : Set α}
    (h : IsFundamentalDomain Γ S μ) (hμ : μ univ ≠ 0) : μ S ≠ 0 := by
  intro h0
  exact hμ (h.measure_zero_of_invariant _ (fun _ => Set.smul_set_univ) (by rw [Set.univ_inter]; exact h0))

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fd (R Γ : Subgroup G) (hR : IsClosed (R : Set G)) (hΓR : Γ ≤ R) [DiscreteTopology Γ] [Countable Γ]
    (K : Set G) (hK : IsCompact K) (hKc : ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ K ∧ D ⊆ (R : Set G) ∧ (∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ D) ∧
      (∀ r ∈ D, ∀ s ∈ Γ, s * r ∈ D → s = 1) := by
  classical
  obtain ⟨sB, ⟨e0⟩⟩ := MeasurableSpace.measurableEquiv_nat_bool_of_countablyGenerated G
  obtain ⟨g0, hg0⟩ := MeasureTheory.exists_measurableEmbedding_real (ℕ → Bool)

  let f : G → ℝ := fun x => g0 (e0 x : ℕ → Bool)
  have hfm : Measurable f := hg0.measurable.comp (measurable_subtype_coe.comp e0.measurable)
  have hfi : Function.Injective f := fun x y hxy => e0.injective (Subtype.ext (hg0.injective hxy))
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete

  have hfin : ∀ r : G, {t : G | t ∈ Γ ∧ t * r ∈ K}.Finite := by
    intro r
    have hc : IsCompact ((Homeomorph.mulRight r) ⁻¹' K) := (Homeomorph.mulRight r).isCompact_preimage.2 hK
    have h1 : IsCompact ((Subtype.val : Γ → G) ⁻¹' ((Homeomorph.mulRight r) ⁻¹' K)) :=
      hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hc
    refine (h1.finite_of_discrete.image Subtype.val).subset ?_
    rintro t ⟨htΓ, htK⟩
    exact ⟨⟨t, htΓ⟩, htK, rfl⟩

  let D : Set G := K ∩ (R : Set G) ∩ {x | ∀ s ∈ Γ, s * x ∈ K → f x ≤ f (s * x)}
  have hDm : MeasurableSet D := by
    refine (hK.measurableSet.inter hR.measurableSet).inter ?_
    have e : {x : G | ∀ s ∈ Γ, s * x ∈ K → f x ≤ f (s * x)} =
        ⋂ s : Γ, ({x : G | (s : G) * x ∈ K}ᶜ ∪ {x | f x ≤ f ((s : G) * x)}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · intro h s
        by_cases hk : (s : G) * x ∈ K
        · exact Or.inr (h s s.2 hk)
        · exact Or.inl hk
      · intro h s hs hk
        exact (h ⟨s, hs⟩).resolve_left (fun hc => hc hk)
    rw [e]
    refine MeasurableSet.iInter fun s => ?_
    refine MeasurableSet.union ?_ ?_
    · exact ((measurable_const_mul (s : G)) hK.measurableSet).compl
    · exact measurableSet_le hfm (hfm.comp (measurable_const_mul _))
  refine ⟨D, hDm, fun x hx => hx.1.1, fun x hx => hx.1.2, ?_, ?_⟩
  · intro r hr
    obtain ⟨s0, hs0, hs0K⟩ := hKc r hr
    obtain ⟨t, ⟨htΓ, htK⟩, hmin⟩ :=
      Set.exists_min_image {t : G | t ∈ Γ ∧ t * r ∈ K} (fun t => f (t * r)) (hfin r) ⟨s0, hs0, hs0K⟩
    refine ⟨t, htΓ, ⟨htK, R.mul_mem (hΓR htΓ) hr⟩, ?_⟩
    intro s hs hsK
    have hle := hmin (s * t) ⟨Γ.mul_mem hs htΓ, by rw [mul_assoc]; exact hsK⟩
    simpa only [mul_assoc] using hle
  · intro r hr s hs hsr
    have h1 : f r ≤ f (s * r) := hr.2 s hs hsr.1.1
    have h2 : f (s * r) ≤ f (s⁻¹ * (s * r)) :=
      hsr.2 s⁻¹ (Γ.inv_mem hs) (by rw [inv_mul_cancel_left]; exact hr.1.1)
    rw [inv_mul_cancel_left] at h2
    have e : s * r = r := hfi (le_antisymm h2 h1)
    calc s = s * r * r⁻¹ := (mul_inv_cancel_right s r).symm
      _ = r * r⁻¹ := by rw [e]
      _ = 1 := mul_inv_cancel r

end Formalism.L2.SG.AvgPf
