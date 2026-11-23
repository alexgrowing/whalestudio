import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal Pointwise

namespace GlobalTheory.QuadricHaar

theorem exists_const {G H X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (a : G → X → X) (a_mul : ∀ g h x, a (g * h) x = a g (a h x)) (a_one : ∀ x, a 1 x = x)
    (a_meas : ∀ g, Measurable (a g)) (x₀ : X) (a_cont : Continuous fun g => a g x₀)
    (S : X → Prop) (j : H →* G) (ν : Measure X) (μ : Measure G) (μ' : Measure H)
    (hj : IsClosedEmbedding j) (hr : Set.range j = {g | a g x₀ = x₀})
    [IsFiniteMeasureOnCompacts ν] (hS : ∀ᵐ y ∂ν, S y) (hν : ∀ g, ν.map (a g) = ν)
    [μ.IsHaarMeasure] [μ'.IsHaarMeasure] :
    ∃ κ : ℝ≥0, ∀ s : X → G, (Measurable s ∧ ∀ y, S y → a (s y) x₀ = y) →
      ∀ f : G → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  by_cases hex : ∃ s : X → G, Measurable s ∧ ∀ y, S y → a (s y) x₀ = y
  swap
  · exact ⟨0, fun s hs => (hex ⟨s, hs⟩).elim⟩
  obtain ⟨s₀, hs₀, hs₀'⟩ := hex
  have hjm : Measurable j := hj.continuous.measurable
  have key : ∀ (f : G → ℝ≥0∞) (b c : G), a b x₀ = a c x₀ →
      ∫⁻ g', f (b * j g') ∂μ' = ∫⁻ g', f (c * j g') ∂μ' := by
    intro f b c h
    have : b⁻¹ * c ∈ Set.range j := by
      rw [hr]
      change a (b⁻¹ * c) x₀ = x₀
      rw [a_mul, ← h, ← a_mul, inv_mul_cancel, a_one]
    obtain ⟨k, hk⟩ := this
    rw [← lintegral_mul_left_eq_self (fun g' => f (b * j g')) k]
    refine lintegral_congr fun g' => ?_
    rw [map_mul, hk, ← mul_assoc, mul_inv_cancel_left]
  have hp : Measurable fun p : X × H => s₀ p.1 * j p.2 :=
    (hs₀.comp measurable_fst).mul (hjm.comp measurable_snd)
  set m : Measure G := (ν.prod μ').map fun p : X × H => s₀ p.1 * j p.2 with hm
  have hint : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂m = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
    intro f hf
    rw [hm, lintegral_map hf hp]
    exact lintegral_prod _ (hf.comp hp).aemeasurable
  have hmeas : ∀ f : G → ℝ≥0∞, Measurable f →
      Measurable fun y => ∫⁻ g', f (s₀ y * j g') ∂μ' := fun f hf =>
    (hf.comp hp).lintegral_prod_right'
  haveI : m.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul h),
      hint (fun g => f (h * g)) (hf.comp (measurable_const_mul h)), hint f hf]
    have e : ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν =
        ∫⁻ y, (∫⁻ g', f (s₀ (a h y) * j g') ∂μ') ∂ν := by
      conv_lhs => rw [← hν h]
      rw [lintegral_map (hmeas f hf) (a_meas h)]
    rw [e]
    have hS' : ∀ᵐ y ∂ν, S (a h y) := by
      refine ae_of_ae_map (p := S) (a_meas h).aemeasurable ?_
      rw [hν h]; exact hS
    refine lintegral_congr_ae ?_
    filter_upwards [hS, hS'] with y h1 h2
    rw [← key f (h * s₀ y) _ (by rw [a_mul, hs₀' y h1, hs₀' _ h2])]
    simp only [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g => a g x₀) '' K) := hK.image a_cont
    have hC : IsCompact (j ⁻¹' (K⁻¹ * K)) := hj.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, hint _ (measurable_one.indicator hKm)]
    have hle : ∀ᵐ y ∂ν, ∫⁻ g', K.indicator (1 : G → ℝ≥0∞) (s₀ y * j g') ∂μ' ≤
        ((fun g => a g x₀) '' K).indicator (fun _ => μ' (j ⁻¹' (K⁻¹ * K))) y := by
      filter_upwards [hS] with y hy
      by_cases hyL : y ∈ (fun g => a g x₀) '' K
      · rw [Set.indicator_of_mem hyL]
        obtain ⟨b, hb, hby⟩ := hyL
        rw [key _ (s₀ y) b (by rw [hs₀' y hy]; exact hby.symm),
          ← lintegral_indicator_one hC.measurableSet]
        refine lintegral_mono fun g' => ?_
        by_cases hg : b * j g' ∈ K
        · have : g' ∈ j ⁻¹' (K⁻¹ * K) :=
            ⟨b⁻¹, by simpa using hb, b * j g', hg, by simp⟩
          simp [Set.indicator_of_mem hg, Set.indicator_of_mem this]
        · simp [Set.indicator_of_notMem hg]
      · rw [Set.indicator_of_notMem hyL]
        refine le_of_eq ((lintegral_congr fun g' => ?_).trans lintegral_zero)
        refine Set.indicator_of_notMem (fun hg => hyL ⟨_, hg, ?_⟩) _
        have : j g' ∈ {g | a g x₀ = x₀} := hr ▸ Set.mem_range_self g'
        change a (s₀ y * j g') x₀ = y
        rw [a_mul, this, hs₀' y hy]
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_indicator_const hL.measurableSet]
    exact ENNReal.mul_lt_top hC.measure_lt_top hL.measure_lt_top
  refine ⟨Measure.haarScalarFactor m μ, fun s hs f hf => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul m μ
  calc ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν
      = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hS] with y hy
        exact key f _ _ (by rw [hs.2 y hy, hs₀' y hy])
    _ = ∫⁻ g, f g ∂m := (hint f hf).symm
    _ = _ := by
        conv_lhs => rw [e]
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem quadric_haar : ∀ (P Q P' Q' : ℕ) (β : ℝ) (x₀ : Sp P Q) (j : UpqT P' Q' →* UpqT P Q)
    (ν : Measure (Sp P Q)) (μ : Measure (UpqT P Q)) (μ' : Measure (UpqT P' Q')),
    Topology.IsClosedEmbedding j → Set.range j = {g | act g x₀ = x₀} →
    IsFiniteMeasureOnCompacts ν → (∀ᵐ y ∂ν, qf y = β) → (∀ g : UpqT P Q, ν.map (act g) = ν) →
    μ.IsHaarMeasure → μ'.IsHaarMeasure →
    ∃ κ : ℝ≥0, ∀ s : Sp P Q → UpqT P Q, IsSection β x₀ s →
      ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  intro P Q P' Q' β x₀ j ν μ μ' hj hr h1 hS hν h2 h3
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  refine exists_const act (fun g h x => ?_) (fun x => Matrix.one_mulVec x) (fun g => ?_) x₀ ?_
    (fun y => qf y = β) j ν μ μ' hj hr hS hν
  · exact (Matrix.mulVec_mulVec x (UpqT.mat g) (UpqT.mat h)).symm
  · exact (continuous_const.matrix_mulVec continuous_id).measurable
  · exact GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

end GlobalTheory.QuadricHaar
