import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem translate_inter_null {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    (μ : Measure G) (fund : Set G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) (hf : MeasurableSet fund)
    (hd : ∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hab : a ≠ b) :
    μ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 := by
  have hc : a⁻¹ * b ∈ Γ := Γ.mul_mem (Γ.inv_mem ha) hb
  have hc1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
  have hset : (fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund
      ⊆ (fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨b⁻¹ * y, h2, ?_⟩, h1⟩
    show a⁻¹ * b * (b⁻¹ * y) = a⁻¹ * y
    group
  refine measure_mono_null hset (nonpos_iff_eq_zero.mp ?_)
  calc μ ((fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund))
      ≤ μ.map (fun y => a⁻¹ * y) ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) :=
        MeasureTheory.Measure.le_map_apply (measurable_const_mul _).aemeasurable _
    _ = 0 := by rw [hμ _ (Γ.inv_mem ha)]; exact hd _ hc hc1

private theorem withDensity_preimage_inv_mul_eq_setLIntegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (a : G) (hμa : μ.map (fun y => a * y) = μ)
    (fund : Set G) (hf : MeasurableSet fund) :
    μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund) = ∫⁻ g in fund, Φ (a * g) ∂μ := by
  classical
  have hT : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) := hf.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, ← lintegral_indicator hT, ← lintegral_indicator hf]
  have hm : Measurable (((fun y => a⁻¹ * y) ⁻¹' fund).indicator Φ) := hΦ.indicator hT
  have key := MeasureTheory.lintegral_map (μ := μ) hm (measurable_const_mul a)
  rw [hμa] at key
  rw [key]
  congr 1
  funext x
  by_cases hx : x ∈ fund
  · have hx' : a * x ∈ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∈ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : a * x ∉ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∉ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hx', if_neg hx]

private theorem withDensity_preimage_mul_eq_of_invariant {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (s : G) (hμs : μ.map (fun y => s * y) = μ)
    (hΦs : ∀ g, Φ (s * g) = Φ g) (Q : Set G) (hQ : MeasurableSet Q) :
    μ.withDensity Φ ((fun y => s * y) ⁻¹' Q) = μ.withDensity Φ Q := by
  classical
  have hT : MeasurableSet ((fun y => s * y) ⁻¹' Q) := hQ.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, withDensity_apply _ hQ, ← lintegral_indicator hT, ← lintegral_indicator hQ]
  have key := MeasureTheory.lintegral_map (μ := μ) (hΦ.indicator hQ) (measurable_const_mul s)
  rw [hμs] at key
  rw [key]
  congr 1
  funext y
  by_cases hy : s * y ∈ Q
  · have hy' : y ∈ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, hΦs]
  · have hy' : y ∉ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hy', if_neg hy]

theorem lintegral_tsum_cosets_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  intro G _ _ _ Γ S μ fund Φ ι _ r hΓ hSΓ hμ hf hcov hd hΦ hΦS hr hrep
  have hTm : ∀ a : G, MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) :=
    fun a => hf.preimage (measurable_const_mul _)
  have hSc : (S : Set G).Countable := hΓ.mono hSΓ
  have hD0m : MeasurableSet (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := MeasurableSet.iUnion fun i => hTm _
  have hnull : ∀ a b : G, a ∈ Γ → b ∈ Γ → a ≠ b →
      μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 :=
    fun a b ha hb hab => withDensity_absolutelyContinuous μ Φ
      (translate_inter_null Γ μ fund hμ hf hd ha hb hab)
  have hL : ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ
      = μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := by
    rw [lintegral_tsum (f := fun i g => Φ (r i * g)) fun i => (hΦ.comp (measurable_const_mul (r i))).aemeasurable]
    rw [measure_iUnion₀ ?_ fun i => (hTm _).nullMeasurableSet]
    · exact tsum_congr fun i =>
        (withDensity_preimage_inv_mul_eq_setLIntegral μ Φ hΦ (r i) (hμ _ (hr i)) fund hf).symm
    · intro i j hij
      refine hnull _ _ (hr i) (hr j) fun he => hij ?_
      have h1 : r i * (r i)⁻¹ ∈ S := by simpa using S.one_mem
      exact (hrep _ (hr i)).unique h1 (by rw [he]; simpa using S.one_mem)
  rw [hL]
  unfold GlobalTheory.FlagMeas.covol
  apply le_antisymm
  · refine le_iInf fun D => le_iInf fun hDm => le_iInf fun hDc => ?_
    calc μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund)
        ≤ μ.withDensity Φ (⋃ s ∈ (S : Set G), (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => s * y) ⁻¹' D) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨s, hs, hsx⟩ := hDc x (Set.mem_univ x)
          exact Set.mem_biUnion hs ⟨hx, hsx⟩
      _ ≤ ∑' p : (S : Set G), μ.withDensity Φ ((⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => (p : G) * y) ⁻¹' D) :=
          measure_biUnion_le _ hSc _
      _ = ∑' p : (S : Set G), μ.withDensity Φ ((fun y => (p : G)⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine tsum_congr fun p => ?_
          have hpS : (p : G) ∈ S := p.2
          rw [← withDensity_preimage_mul_eq_of_invariant μ Φ hΦ (p : G) (hμ _ (hSΓ hpS)) (fun g => hΦS _ hpS g) _
            ((hD0m.preimage (measurable_const_mul _)).inter hDm)]
          congr 1
          ext y
          simp only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]
      _ = μ.withDensity Φ (⋃ s ∈ (S : Set G), (fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine (measure_biUnion₀ hSc ?_ fun s _ =>
            ((hD0m.preimage (measurable_const_mul _)).inter hDm).nullMeasurableSet).symm
          intro s hs s' hs' hne
          have hsub : ((fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ∩
              ((fun y => s'⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ⊆
              ⋃ i, ⋃ j, (fun y => (s * r i)⁻¹ * y) ⁻¹' fund ∩ (fun y => (s' * r j)⁻¹ * y) ⁻¹' fund := by
            rintro y ⟨⟨hy1, -⟩, hy2, -⟩
            simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 hy2
            obtain ⟨i, hi⟩ := hy1
            obtain ⟨j, hj⟩ := hy2
            simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, _root_.mul_inv_rev, mul_assoc]
            exact ⟨i, j, hi, hj⟩
          refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun j => ?_)
          refine hnull _ _ (Γ.mul_mem (hSΓ hs) (hr i)) (Γ.mul_mem (hSΓ hs') (hr j)) fun he => hne ?_
          have h1 : s * r i * (r i)⁻¹ ∈ S := by rw [mul_inv_cancel_right]; exact hs
          have h2 : s * r i * (r j)⁻¹ ∈ S := by rw [he, mul_inv_cancel_right]; exact hs'
          have hij := (hrep _ (Γ.mul_mem (hSΓ hs) (hr i))).unique h1 h2
          subst hij
          exact mul_right_cancel he
      _ ≤ μ.withDensity Φ D := measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_right)
  · refine iInf_le_of_le _ (iInf_le_of_le hD0m (iInf_le _ ?_))
    intro x _
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    obtain ⟨i, hi, -⟩ := hrep γ⁻¹ (Γ.inv_mem hγ)
    refine ⟨(γ⁻¹ * (r i)⁻¹)⁻¹, S.inv_mem hi, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    show (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) ∈ fund
    have e : (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) = γ * x := by group
    rw [e]; exact hγx

end GlobalTheory.StabUnfold
