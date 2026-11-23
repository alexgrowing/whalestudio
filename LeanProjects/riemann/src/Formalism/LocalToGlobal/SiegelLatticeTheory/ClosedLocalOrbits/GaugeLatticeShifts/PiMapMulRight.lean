import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralFinProd

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

section Dens

variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem pi_withDensity (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (ae_of_all _ (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_prod _ _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

theorem pi_conc (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (S : ∀ i, Set (α i))
    (h : ∀ i, μ i (S i)ᶜ = 0) : Measure.pi μ (Set.univ.pi S)ᶜ = 0 := by
  have hsub : (Set.univ.pi S)ᶜ ⊆ ⋃ i, Function.eval i ⁻¹' (S i)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  exact measure_mono_null hsub (measure_iUnion_null fun i => Measure.pi_eval_preimage_null (μ := μ) (h i))

theorem pi_ne_zero (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, μ i ≠ 0) : Measure.pi μ ≠ 0 := by
  intro h0
  have h1 := congrArg (fun ν : Measure (∀ i, α i) => ν Set.univ) h0
  simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h1
  exact h i (Measure.measure_univ_eq_zero.1 hi)

end Dens

section Grp

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableMul (G i)]

theorem pi_map_mul_left (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, G i)
    (h : ∀ i, (μ i).map (fun x => g i * x) = μ i) : (Measure.pi μ).map (fun x => g * x) = Measure.pi μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hm : Measurable (fun x : ∀ i, G i => g * x) :=
    measurable_pi_lambda _ fun i => (measurable_const_mul (g i)).comp (measurable_pi_apply i)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ i, G i => g * x) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => (fun y => g i * y) ⁻¹' s i := by
    ext x; simp [Set.mem_univ_pi]
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Measure.map_apply (measurable_const_mul (g i)) (hs i), h i]

theorem pi_map_mul_right (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, G i)
    (h : ∀ i, (μ i).map (fun x => x * g i) = μ i) : (Measure.pi μ).map (fun x => x * g) = Measure.pi μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hm : Measurable (fun x : ∀ i, G i => x * g) :=
    measurable_pi_lambda _ fun i => (measurable_mul_const (g i)).comp (measurable_pi_apply i)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ i, G i => x * g) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => (fun y => y * g i) ⁻¹' s i := by
    ext x; simp [Set.mem_univ_pi]
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Measure.map_apply (measurable_mul_const (g i)) (hs i), h i]

end Grp

section Uniq

theorem exists_pos_fin {β : Type*} [MeasurableSpace β] (ν : Measure β) [SigmaFinite ν] (h : ν ≠ 0) :
    ∃ t, MeasurableSet t ∧ ν t ≠ 0 ∧ ν t ≠ ∞ := by
  by_contra hne
  push_neg at hne
  apply h
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  by_contra hn
  exact (measure_spanningSets_lt_top ν n).ne (hne _ (measurableSet_spanningSets ν n) hn)

theorem uniq_on_closed {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ ν : Measure G)
    [SigmaFinite μ] [SigmaFinite ν] (hμc : μ (H : Set G)ᶜ = 0) (hνc : ν (H : Set G)ᶜ = 0)
    (hμi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) (hνi : ∀ h ∈ H, ν.map (fun x => h * x) = ν) (hμ0 : μ ≠ 0)
    (hν0 : ν ≠ 0) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ = κ • ν := by
  classical
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  have he : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hHm
  have hback : ∀ (m : Measure G), m (H : Set G)ᶜ = 0 →
      (m.comap (Subtype.val : H → G)).map Subtype.val = m := by
    intro m hm
    rw [he.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    convert hm using 2
    ext x
    simp
  have hinv : ∀ (m : Measure G), (∀ h ∈ H, m.map (fun x => h * x) = m) →
      (m.comap (Subtype.val : H → G)).IsMulLeftInvariant := by
    intro m hm
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, he.comap_apply, he.comap_apply]
    have himg : Subtype.val '' ((fun x : H => g * x) ⁻¹' s) =
        (fun x : G => (g : G) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have hx : x ∈ H := by
          have hx' : x = (g : G)⁻¹ * (y : G) := by rw [hxy, inv_mul_cancel_left]
          rw [hx']
          exact H.mul_mem (H.inv_mem g.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have hgy : g * (⟨x, hx⟩ : H) = y := Subtype.ext (by rw [Subgroup.coe_mul]; exact hxy.symm)
        rw [hgy]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (g : G)) (he.measurableSet_image.2 hs),
      hm g g.2]
  have hsf : ∀ (m : Measure G) [SigmaFinite m], m (H : Set G)ᶜ = 0 →
      SigmaFinite (m.comap (Subtype.val : H → G)) := by
    intro m _ hm
    refine SigmaFinite.of_map _ he.measurable.aemeasurable ?_
    rw [hback m hm]
    infer_instance
  have hne : ∀ (m : Measure G), m (H : Set G)ᶜ = 0 → m ≠ 0 → m.comap (Subtype.val : H → G) ≠ 0 := by
    intro m hm h0 h
    apply h0
    rw [← hback m hm, h, Measure.map_zero]
  haveI := hsf μ hμc
  haveI := hsf ν hνc
  haveI := hinv μ hμi
  haveI := hinv ν hνi
  obtain ⟨t, -, htν0, htνi⟩ := exists_pos_fin (ν.comap (Subtype.val : H → G)) (hne ν hνc hν0)
  obtain ⟨t', -, htμ0, htμi⟩ := exists_pos_fin (μ.comap (Subtype.val : H → G)) (hne μ hμc hμ0)
  haveI : BorelSpace H := Subtype.borelSpace _
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : MeasurableMul₂ H := ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := ContinuousInv.measurableInv
  have key := measure_eq_div_smul (μ.comap (Subtype.val : H → G)) (ν.comap (Subtype.val : H → G)) htν0 htνi
  set κ := μ.comap (Subtype.val : H → G) t / ν.comap (Subtype.val : H → G) t with hκ
  have hval := congrArg (fun m : Measure H => m t') key
  simp only [Measure.smul_apply, smul_eq_mul] at hval
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hval
    exact htμ0 hval
  · intro hi
    rw [hi] at hval
    by_cases h : ν.comap (Subtype.val : H → G) t' = 0
    · rw [h, mul_zero] at hval
      exact htμ0 hval
    · rw [ENNReal.top_mul h] at hval
      exact htμi hval
  · conv_lhs => rw [← hback μ hμc, key]
    rw [Measure.map_smul, hback ν hνc]

end Uniq

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
