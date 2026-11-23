import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient

open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def HaarQK : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (νQ : Measure Q) [νQ.IsHaarMeasure] (κ : Measure K) [κ.IsHaarMeasure],
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G))

private theorem cancel_lemma_0 {a b s : ℝ≥0∞} (h0 : s ≠ 0) (ht : s ≠ ⊤) (h : s * a = s * b) : a = b := by
  calc a = s⁻¹ * (s * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ = s⁻¹ * (s * b) := by rw [h]
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

private theorem mapMulRight_lemma {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H]
    (ν : Measure H) [ν.IsMulLeftInvariant] (a : H) : (ν.map (· * a)).IsMulLeftInvariant := by
  constructor
  intro b
  rw [Measure.map_map (measurable_const_mul b) (measurable_mul_const a)]
  rw [show ((b * ·) ∘ (· * a)) = ((· * a) ∘ (b * ·)) from funext fun x => (mul_assoc b x a).symm]
  rw [← Measure.map_map (measurable_mul_const a) (measurable_const_mul b), MeasureTheory.map_mul_left_eq_self]

private theorem cptRight_lemma_2 {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (κ : Measure H) [κ.IsHaarMeasure] : κ.IsMulRightInvariant := by
  constructor
  intro a
  haveI := mapMulRight_lemma κ a
  have h := Measure.isMulLeftInvariant_eq_smul (κ.map (· * a)) κ
  have hu := congrArg (fun ν : Measure H => ν Set.univ) h
  simp only [Measure.map_apply (measurable_mul_const a) MeasurableSet.univ, Set.preimage_univ,
    Measure.nnreal_smul_coe_apply] at hu
  have h0 : κ Set.univ ≠ 0 := (isOpen_univ.measure_pos κ Set.univ_nonempty).ne'
  have ht : κ Set.univ ≠ ⊤ := measure_ne_top κ _
  have hc : ((κ.map (· * a)).haarScalarFactor κ : ℝ≥0∞) = 1 :=
    cancel_lemma_0 h0 ht (by rw [mul_one, mul_comm]; exact hu.symm)
  rw [h, show (κ.map (· * a)).haarScalarFactor κ = 1 from ENNReal.coe_eq_one.1 hc, one_smul]

theorem haarQK : HaarQK := by
  unfold HaarQK
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hQK νQ _ κ _
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : κ.IsMulRightInvariant := cptRight_lemma_2 κ
  have hνR : ∀ q0 : Q, ∃ c : NNReal, νQ.map (· * q0) = c • νQ := by
    intro q0
    haveI := mapMulRight_lemma νQ q0
    haveI : IsFiniteMeasureOnCompacts (νQ.map (· * q0)) := ⟨fun C hC => by
      rw [Measure.map_apply (measurable_mul_const q0) hC.measurableSet]
      exact ((Homeomorph.mulRight q0).isCompact_preimage.2 hC).measure_lt_top⟩
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul (νQ.map (· * q0)) νQ⟩
  have hT : ∀ g : G, ∃ c : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        c * ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) := by
    intro g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    obtain ⟨c, hc⟩ := hνR ⟨q0, hq0⟩
    refine ⟨(c : ℝ≥0∞), fun f hf => ?_⟩
    have hF : Measurable (fun p : Q × K => f ((p.1 : G) * (p.2 : G))) := by fun_prop
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ hF.aemeasurable]
    have h1 : ∀ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ =
        ∫⁻ k : K, f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G)) ∂κ := by
      intro q
      rw [← lintegral_mul_left_eq_self (fun k : K => f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G))) ⟨k0, hk0⟩]
      congr 1
      funext k
      simp [mul_assoc]
    calc ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) (q * ⟨q0, hq0⟩) ∂νQ :=
          lintegral_congr fun q => h1 q
      _ = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) q ∂(νQ.map (· * ⟨q0, hq0⟩)) :=
          (lintegral_map hF.lintegral_prod_right' (measurable_mul_const _)).symm
      _ = (c : ℝ≥0∞) * ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (k : G)) ∂κ ∂νQ := by
          rw [hc, lintegral_smul_measure]
          rfl

  have hswap : ∀ f φ : G → ℝ≥0∞, Measurable f → Measurable φ →
      ∫⁻ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ =
        ∫⁻ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) ∂μ := by
    intro f φ hf hφ
    have e1 : ∀ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ g * f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    have e2 : ∀ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    rw [lintegral_congr e1, lintegral_congr e2]
    have m1 : Measurable (fun p : G × (Q × K) => φ p.1 * f ((p.2.1 : G) * p.1 * (p.2.2 : G))) := by fun_prop
    have m2 : Measurable (fun p : G × (Q × K) => f p.1 * φ ((p.2.1 : G)⁻¹ * p.1 * (p.2.2 : G)⁻¹)) := by fun_prop
    rw [lintegral_lintegral_swap m1.aemeasurable]
    conv_rhs => rw [lintegral_lintegral_swap m2.aemeasurable]
    refine lintegral_congr fun h => ?_
    have inv : ∀ F : G → ℝ≥0∞, ∫⁻ g, F ((h.1 : G) * g * (h.2 : G)) ∂μ = ∫⁻ g, F g ∂μ := by
      intro F
      rw [lintegral_mul_left_eq_self (fun x => F (x * (h.2 : G))) (h.1 : G),
        lintegral_mul_right_eq_self F (h.2 : G)]
    rw [← inv (fun g => f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹))]
    refine lintegral_congr fun g => ?_
    rw [mul_comm]
    simp [mul_assoc]
  have hS : ∀ φ : G → ℝ≥0∞, Measurable φ → ∀ g : G,
      ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) := by
    intro φ hφ g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    have hin : ∀ x : G, ∫⁻ k : K, φ (x * k0 * (k : G)⁻¹) ∂κ = ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ := by
      intro x
      rw [← lintegral_mul_right_eq_self (fun k : K => φ (x * k0 * (k : G)⁻¹)) ⟨k0, hk0⟩]
      refine lintegral_congr fun k => ?_
      simp [mul_assoc]
    have hΨ : Measurable (fun p : G × K => φ (p.1 * (p.2 : G)⁻¹)) := by fun_prop
    calc ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (q0 * k0) * (k : G)⁻¹) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0) ∂νQ := by
          refine lintegral_congr fun q => ?_
          show _ = ∫⁻ k : K, φ ((q : G)⁻¹ * q0 * (k : G)⁻¹) ∂κ
          rw [← hin ((q : G)⁻¹ * q0)]
          simp only [mul_assoc]
      _ = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ)
            (((⟨q0, hq0⟩ * q : Q) : G)⁻¹ * q0) ∂νQ :=
          (lintegral_mul_left_eq_self
            (fun q : Q => (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0)) ⟨q0, hq0⟩).symm
      _ = ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (k : G)⁻¹) ∂κ ∂νQ := by
          refine lintegral_congr fun q => ?_
          simp [mul_assoc]

  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have h1C : (1 : G) ∈ interior C := mem_interior_iff_mem_nhds.2 hC1
  obtain ⟨f0, hf0⟩ : ∃ f0 : G → ℝ≥0∞, f0 = C.indicator 1 := ⟨_, rfl⟩
  have hf0m : Measurable f0 := hf0 ▸ measurable_one.indicator hCm
  have hΦm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΦc : Continuous (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΨm : Measurable (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  have hΨc : Continuous (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Measure G, ρ = (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)) := ⟨_, rfl⟩
  have hPρ : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) = ∫⁻ g, f g ∂ρ := fun f hf => by
    rw [hρ, lintegral_map hf hΦm]
  have hρC : ρ C = (νQ.prod κ) ((fun p : Q × K => (p.1 : G) * (p.2 : G)) ⁻¹' C) := by
    rw [hρ, Measure.map_apply hΦm hCm]
  have hρCt : ρ C ≠ ⊤ := by
    rw [hρC]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2) '' (C ×ˢ (K : Set G))) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hCc.prod hK).image continuous_mul)).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨((p.1 : G) * (p.2 : G), ((p.2 : K) : G)⁻¹), ⟨hp, K.inv_mem p.2.2⟩, by simp⟩
  have hρC0 : ρ C ≠ 0 := by
    rw [hρC]
    exact ((isOpen_interior.preimage hΦc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'
  have hμCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hμC0 : μ C ≠ 0 :=
    ((isOpen_interior.measure_pos μ ⟨1, h1C⟩).trans_le (measure_mono interior_subset)).ne'
  have hs : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
      (νQ.prod κ) ((fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) ⁻¹' C) := by
    rw [lintegral_map (f := f0) hf0m hΨm |>.symm, hf0, lintegral_indicator_one hCm, Measure.map_apply hΨm hCm]
  have hst : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ ⊤ := by
    rw [hs]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2⁻¹) '' ((K : Set G) ×ˢ C)) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hK.prod hCc).image (by fun_prop))).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨(((p.2 : K) : G)⁻¹, (p.1 : G)⁻¹ * (p.2 : G)⁻¹), ⟨K.inv_mem p.2.2, hp⟩, by group⟩
  have hs0 : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ 0 := by
    rw [hs]
    exact ((isOpen_interior.preimage hΨc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'

  have hμf0 : ∫⁻ g, f0 g ∂μ = μ C := by rw [hf0, lintegral_indicator_one hCm]
  have hρf0 : ∫⁻ g, f0 g ∂ρ = ρ C := by rw [hf0, lintegral_indicator_one hCm]
  choose c hc using hT
  have hTm : Measurable (fun g : G => ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) :=
    (by fun_prop : Measurable (fun p : G × (Q × K) => f0 ((p.2.1 : G) * p.1 * (p.2.2 : G)))).lintegral_prod_right'
  have key : ∀ f : G → ℝ≥0∞, Measurable f → (∫⁻ g, f g ∂μ) * ρ C = μ C * ∫⁻ g, f g ∂ρ := by
    intro f hf
    set s0 := ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) with hs0def
    have A := hswap f f0 hf hf0m
    have B := hswap f0 f0 hf0m hf0m
    simp only [hS f0 hf0m] at A B
    rw [lintegral_mul_const _ hf] at A
    rw [lintegral_mul_const _ hf0m, hμf0] at B
    have e : ∀ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C =
        f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ∫⁻ x, f x ∂ρ := by
      intro g
      rw [hc g f hf, hc g f0 hf0m, hPρ f hf, hPρ f0 hf0m, hρf0]
      ring
    have hmain : s0 * ((∫⁻ g, f g ∂μ) * ρ C) = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by
      calc s0 * ((∫⁻ g, f g ∂μ) * ρ C) = (∫⁻ g, f g ∂μ) * s0 * ρ C := by ring
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) * ρ C := by
            rw [A]
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C ∂μ :=
            (lintegral_mul_const' _ _ hρCt).symm
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) *
              ∫⁻ x, f x ∂ρ ∂μ := lintegral_congr e
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) *
              ∫⁻ x, f x ∂ρ := lintegral_mul_const _ (hf0m.mul hTm)
        _ = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by rw [B]; ring
    exact cancel_lemma_0 hs0 hst hmain
  refine ⟨μ C * (ρ C)⁻¹, mul_ne_zero hμC0 (ENNReal.inv_ne_zero.2 hρCt),
    ENNReal.mul_ne_top hμCt (ENNReal.inv_ne_top.2 hρC0), ?_⟩
  rw [← hρ]
  ext B hB
  have hk := key (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, lintegral_indicator_one hB] at hk
  rw [Measure.smul_apply, smul_eq_mul]
  calc μ B = μ B * ρ C * (ρ C)⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hρC0 hρCt, mul_one]
    _ = μ C * ρ B * (ρ C)⁻¹ := by rw [hk]
    _ = μ C * (ρ C)⁻¹ * ρ B := by ring

end GlobalTheory.CompanionTheory.QuotVan
