import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.IwasawaAE

theorem lintegral_mul_right_eq_of_equivariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure K) (δ : P → ℝ≥0) (b : G → ℝ≥0∞),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure → μK.IsHaarMeasure →
    (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → Measurable b →
    (∀ g : G, (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ 0 ∧ (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ ∞) →
    ∀ Φ : G → ℝ≥0∞, AEMeasurable Φ μG → (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
    ∀ g : G, ∫⁻ k : K, Φ ((k : G) * g) ∂μK = ∫⁻ k : K, Φ (k : G) ∂μK := by
  intro G _ _ _ _ _ _ _ _ P K μG μP μK δ b hPc hKc hG hPH hKH hright hδ hdec hb hU Φ hΦ hΦeq g
  haveI := hG; haveI := hPH; haveI := hKH
  haveI : LocallyCompactSpace P := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hsurj : Function.Surjective (GroundTheory.Automorphic.HaarSK.mulMap P K) := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := hdec x
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.NAK.exists_eq_smul_map_mulMap_of_right P K μG (fun k _ => hright k) hPc hKc hsurj μP μK
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 := (isOpen_univ (X := G)).measure_pos μG Set.univ_nonempty
    rw [hc] at h0
    simp at h0
  have hm : Measurable (GroundTheory.Automorphic.HaarSK.mulMap P K) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  set M := Measure.map (GroundTheory.Automorphic.HaarSK.mulMap P K) (μP.prod μK) with hM
  have hMG : M = c⁻¹ • μG := by rw [hc, inv_smul_smul₀ hc0]
  have hmeas : ∀ h : G, Measurable (fun z : P × K => (z.1 : G) * z.2 * h) := fun h =>
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)).mul_const h
  have hmap : ∀ h : G, Measure.map (fun z : P × K => (z.1 : G) * z.2 * h) (μP.prod μK) = M := by
    intro h
    have e : (fun z : P × K => (z.1 : G) * z.2 * h) = (· * h) ∘ GroundTheory.Automorphic.HaarSK.mulMap P K := by
      funext z; rfl
    rw [e, ← Measure.map_map (measurable_mul_const h) hm, ← hM, hMG, Measure.map_smul, hright]
  set U : G → ℝ≥0∞ := fun x => ∫⁻ q : P, b ((q : G) * x) ∂μP with hUdef
  have hUm : Measurable U :=
    Measurable.lintegral_prod_right' (f := fun z : G × P => b ((z.2 : G) * z.1))
      (hb.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst))
  have hUeq : ∀ (p : P) (x : G), U ((p : G) * x) = (δ p : ℝ≥0∞) * U x := by
    intro p x
    have hf : Measurable (fun q : P => b ((q : G) * x)) := hb.comp (measurable_subtype_coe.mul_const x)
    calc U ((p : G) * x) = ∫⁻ q : P, b (((q * p : P) : G) * x) ∂μP := by
          refine lintegral_congr fun q => ?_
          rw [Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ q : P, b ((q : G) * x) ∂(μP.map (· * p)) := (lintegral_map hf (measurable_mul_const p)).symm
      _ = _ := by rw [hδ p, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hδ0 : ∀ p : P, (δ p : ℝ≥0∞) ≠ 0 := by
    intro p h
    have h1 := hUeq p 1
    rw [h, zero_mul, mul_one] at h1
    exact (hU (p : G)).1 h1
  set H : G → ℝ≥0∞ := fun x => b x * (Φ x / U x) with hHdef
  have hkey : ∀ x : G, ∫⁻ q : P, H ((q : G) * x) ∂μP = Φ x := by
    intro x
    have h1 : ∀ q : P, H ((q : G) * x) = b ((q : G) * x) * (Φ x / U x) := by
      intro q
      simp only [hHdef]
      rw [hΦeq, hUeq, ENNReal.mul_div_mul_left _ _ (hδ0 q) ENNReal.coe_ne_top]
    simp_rw [h1]
    rw [lintegral_mul_const (f := fun q : P => b ((q : G) * x)) _ (hb.comp (measurable_subtype_coe.mul_const x))]
    exact ENNReal.mul_div_cancel (hU x).1 (hU x).2
  have hHM : AEMeasurable H M := by
    rw [hMG]; exact (hb.aemeasurable.mul (hΦ.div hUm.aemeasurable)).smul_measure _
  have hall : ∀ h : G, ∫⁻ k : K, Φ ((k : G) * h) ∂μK = ∫⁻ y, H y ∂M := by
    intro h
    have hHh : AEMeasurable H (Measure.map (fun z : P × K => (z.1 : G) * z.2 * h) (μP.prod μK)) := by
      rw [hmap h]; exact hHM
    rw [← hmap h, lintegral_map' hHh (hmeas h).aemeasurable,
      lintegral_prod_symm (fun z : P × K => H ((z.1 : G) * z.2 * h)) (hHh.comp_aemeasurable (hmeas h).aemeasurable)]
    refine lintegral_congr fun k => ?_
    rw [← hkey]
    refine lintegral_congr fun q => ?_
    simp only [mul_assoc]
  rw [hall g, ← hall 1]
  simp only [mul_one]

end GlobalTheory.IwasawaAE
