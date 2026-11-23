import Mathlib
open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory

theorem map_restrict_subgroup_eq_smul_haar (G : Type) [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (hμ : μ H ≠ 0)
    (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Measurable ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t) (hf : ∀ t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ ⁻¹' W) ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ (μ.restrict H).map ψ = κ • ν ∧ ν.IsMulRightInvariant := by
  set m : Measure R := (μ.restrict H).map ψ with hm
  have happ : ∀ s, MeasurableSet s → m s = μ (ψ ⁻¹' s ∩ H) := by
    intro s hs'
    rw [hm, Measure.map_apply hψ hs', Measure.restrict_apply (hψ hs')]
  have hL : m.IsMulLeftInvariant := by
    rw [← forall_measure_preimage_mul_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_const_mul _ hs'), ← measure_preimage_mul μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_left hh]
  have hR : m.IsMulRightInvariant := by
    rw [← forall_measure_preimage_mul_right_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_mul_const _ hs'),
      ← measure_preimage_mul_right μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_right hh]
  have hF : IsLocallyFiniteMeasure m := by
    refine ⟨fun t => ?_⟩
    obtain ⟨W, hW, hW'⟩ := hf t
    refine ⟨interior W, interior_mem_nhds.2 hW, ?_⟩
    rw [happ _ isOpen_interior.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.2 hW')
    intro g hg
    exact ⟨hg.2, interior_subset (s := W) hg.1⟩
  have h0 : m ≠ 0 := by
    intro h
    have := happ Set.univ MeasurableSet.univ
    rw [h] at this
    apply hμ
    simpa using this.symm
  have hκ := Measure.isMulLeftInvariant_eq_smul m ν
  set c := Measure.haarScalarFactor m ν
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact h0 hκ
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  have hκ' : m = (c : ℝ≥0∞) • ν := hκ
  refine ⟨c, hc', ENNReal.coe_ne_top, hκ', ?_⟩
  have : ν = (c : ℝ≥0∞)⁻¹ • m := by
    rw [hκ', smul_smul, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_smul]
  rw [this]
  infer_instance

theorem map_restrict_subgroup_eq_common_smul_haar : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (H : Subgroup G), MeasurableSet (H : Set G) → μ H ≠ 0 → ∀ (ι : Type) (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ g, ψ k' g = e (α (ψ k g))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ k, (μ.restrict H).map (ψ k) = κ • ν k := by
  intro G _ _ _ μ _ _ H hH hμ ι R _ _ _ _ _ _ _ _ ν _ ψ hψ hs hf hc
  choose κ h0 htop hκ hR using fun k =>
    map_restrict_subgroup_eq_smul_haar G μ H hH hμ (R k) (ν k) (ψ k) (hψ k) (hs k) (hf k)
  have key : ∀ k k', κ k = κ k' := by
    intro k k'
    obtain ⟨e, α, u, he, hα, hψe, hαα⟩ := hc k k'
    have := hR k
    have h1 : κ k' • ν k' = (κ k • (ν k).map α).map e := by
      rw [← hκ k', ← Measure.map_smul, ← hκ k, Measure.map_map hα (hψ k),
        Measure.map_map e.measurable (hα.comp (hψ k))]
      congr 1
      funext g
      exact hψe g
    have h2 : κ k' • ν k = κ k • (ν k).map α := by
      have := congrArg (Measure.map e.symm) h1
      rw [Measure.map_smul, (he.symm e).map_eq, MeasurableEquiv.map_symm_map] at this
      exact this
    have h3 : ((ν k).map α).map α = ν k := by
      rw [Measure.map_map hα hα]
      have : α ∘ α = (fun t => t * u) ∘ (fun t => u⁻¹ * t) := funext hαα
      rw [this, ← Measure.map_map (measurable_mul_const u) (measurable_const_mul u⁻¹),
        map_mul_left_eq_self, map_mul_right_eq_self]
    have h4 : κ k' • (ν k).map α = κ k • ν k := by
      have := congrArg (Measure.map α) h2
      rw [Measure.map_smul, Measure.map_smul, h3] at this
      exact this
    have h5 : (κ k' * κ k') • ν k = (κ k * κ k) • ν k := by
      rw [mul_smul, h2, smul_comm, h4, mul_smul]
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (R k)) := inferInstance
    have hK0 : ν k K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior (ν k) K.interior_nonempty).ne'
    have hKt : ν k K ≠ ⊤ := K.isCompact.measure_ne_top
    have h6 := congrArg (fun m : Measure (R k) => m K) h5
    simp only [Measure.smul_apply, smul_eq_mul] at h6
    have h7 : κ k' * κ k' = κ k * κ k := (ENNReal.mul_left_inj hK0 hKt).1 h6
    rcases lt_trichotomy (κ k) (κ k') with h | h | h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne'
    · exact h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, fun k => hι.elim k⟩
  · exact ⟨κ k₀, h0 k₀, htop k₀, fun k => by rw [hκ k, key k k₀]⟩

end GlobalTheory
