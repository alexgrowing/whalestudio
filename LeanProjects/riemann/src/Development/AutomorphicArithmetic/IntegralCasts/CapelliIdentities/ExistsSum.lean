import Mathlib

theorem UpperTheory.Reformulated.B.Qg3.exists_sum.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ {S : Set G},
          IsCompact S →
            ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ),
              ∀ (F : G → ℂ),
                (∀ (g k : G), k ∈ K → F (g * k) = F g) →
                  (∀ g ∉ S, F g = (0 : ℂ)) → ∫ (g : G), F g ∂μ = ∑ x ∈ T, c x * F (r x) := by
  intro G _ _ _ _ _ μ _ K hKo hKc S hS
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hcont : Continuous (QuotientGroup.mk : G → G ⧸ K) := QuotientGroup.continuous_mk
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image hcont).finite_of_discrete
  let C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x}
  have hmem : ∀ (x : G ⧸ K) (g : G), g ∈ C x ↔ (x.out)⁻¹ * g ∈ K := by
    intro x g
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hmeas : ∀ x, MeasurableSet (C x) := fun x =>
    ((isOpen_discrete {x}).preimage hcont).measurableSet
  have hcomp : ∀ x, IsCompact (C x) := by
    intro x
    have h : C x = (fun k => x.out * k) '' (K : Set G) := by
      ext g
      rw [hmem]
      constructor
      · intro h
        exact ⟨_, h, by simp⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
    rw [h]
    exact hKc.image (continuous_const.mul continuous_id)
  refine ⟨hfin.toFinset, fun x => x.out, fun x => (μ.real (C x) : ℂ), ?_⟩
  intro F hF h0
  have hout : ∀ g : G, F (QuotientGroup.mk g : G ⧸ K).out = F g := by
    intro g
    have h := hF (QuotientGroup.mk g : G ⧸ K).out _ ((hmem _ g).1 rfl)
    rw [mul_inv_cancel_left] at h
    exact h.symm
  have hdec : ∀ g, F g = ∑ x ∈ hfin.toFinset, (C x).indicator (fun _ => F x.out) g := by
    intro g
    rw [Finset.sum_eq_single (QuotientGroup.mk g : G ⧸ K)]
    · rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
    · intro x _ hx
      have hg : g ∉ C x := fun h => hx (Eq.symm h)
      rw [Set.indicator_of_notMem hg]
    · intro hg
      rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
      exact h0 g fun hgS => hg (hfin.mem_toFinset.2 ⟨g, hgS, rfl⟩)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hdec),
    MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [MeasureTheory.integral_indicator_const _ (hmeas x), Complex.real_smul]
  · intro x _
    rw [MeasureTheory.integrable_indicator_iff (hmeas x)]
    exact MeasureTheory.integrableOn_const (hcomp x).measure_lt_top.ne
