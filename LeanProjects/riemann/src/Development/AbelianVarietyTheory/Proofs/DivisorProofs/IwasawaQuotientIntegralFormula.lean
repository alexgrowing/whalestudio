import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasurableModificationStatement

open MeasureTheory Measure Set Function
open scoped NNReal ENNReal

namespace GlobalTheory.EquivAEMeas

theorem aemeasurable_of_equivariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure K) (δ : P → ℝ≥0) (U : G → ℝ≥0∞),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure → μK.IsHaarMeasure →
    (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → Measurable U → (∀ g : G, U g ≠ 0 ∧ U g ≠ ∞) →
    (∀ (p : P) (g : G), U ((p : G) * g) = (δ p : ℝ≥0∞) * U g) → (∀ p : P, (p : G) ∈ K → δ p = 1) →
    ∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
    AEMeasurable (fun k : K => Φ (k : G)) μK → AEMeasurable Φ μG := by
  intro G _ _ _ _ _ _ _ _ P K μG μP μK δ U hP hK hμG hμP hμK hright _hδ hsurj hU hU0 hUeq hδ1 Φ hΦ hΦK
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  set M : Subgroup K := P.subgroupOf K with hM
  have hMc : IsClosed (M : Set K) := by
    rw [hM, Subgroup.coe_subgroupOf]; exact hP.preimage continuous_subtype_val
  have hδM : ∀ m ∈ M, ∀ k : K, ∃ p : P, ((m * k : K) : G) = (p : G) * k ∧ δ p = 1 := by
    intro m hm k
    have hm' : ((m : K) : G) ∈ P := Subgroup.mem_subgroupOf.mp hm
    exact ⟨⟨m, hm'⟩, rfl, hδ1 ⟨m, hm'⟩ m.2⟩
  have hφinv : ∀ m ∈ M, ∀ k : K, (fun k : K => Φ (k : G)) (m * k) = (fun k : K => Φ (k : G)) k := by
    intro m hm k
    obtain ⟨p, hp, h1⟩ := hδM m hm k
    simp only [hp, hΦ, h1, ENNReal.coe_one, one_mul]
  have hUinv : ∀ m ∈ M, ∀ k : K, U ((m * k : K) : G) = U k := by
    intro m hm k
    obtain ⟨p, hp, h1⟩ := hδM m hm k
    rw [hp, hUeq, h1, ENNReal.coe_one, one_mul]
  obtain ⟨ψ, N, hψ, hN, hN0, hNinv, hψinv, hφψ⟩ :=
    GlobalTheory.T.invariant_measurable_modification K M μK hMc hμK (fun k : K => Φ (k : G)) hΦK hφinv
  have hex : ∀ g : G, ∃ x : P × K, (x.1 : G) * x.2 = g := fun g => by
    obtain ⟨p, hp, k, hk, rfl⟩ := hsurj g
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  choose dec hdec using hex
  let R : K → ℝ≥0∞ := fun k => ψ k / U k
  let Φh : G → ℝ≥0∞ := fun g => U g * R (dec g).2
  have hdiff : ∀ (p p' : P) (k k' : K), (p : G) * k = p' * k' → ∃ m ∈ M, k' = m * k := by
    intro p p' k k' h
    refine ⟨k' * k⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    have e : ((k' * k⁻¹ : K) : G) = ((p'⁻¹ * p : P) : G) := by
      push_cast
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
    rw [e]; exact (p'⁻¹ * p).2
  have hRinv : ∀ m ∈ M, ∀ k : K, R (m * k) = R k := by
    intro m hm k
    simp only [R, hψinv m hm k, hUinv m hm k]
  have hΦh_mul : ∀ (p : P) (k : K), Φh ((p : G) * k) = U ((p : G) * k) * R k := by
    intro p k
    obtain ⟨m, hm, he⟩ := hdiff p (dec ((p : G) * k)).1 k (dec ((p : G) * k)).2 (hdec _).symm
    simp only [Φh]
    rw [he, hRinv m hm]
  have hRm : Measurable R := hψ.div (hU.comp measurable_subtype_coe)
  have hmm : Measurable (GroundTheory.Automorphic.HaarSK.mulMap P K) :=
    GroundTheory.Automorphic.HaarSK.continuous_mulMap.measurable
  have hsurj' : Surjective (GroundTheory.Automorphic.HaarSK.mulMap P K) := fun g => ⟨dec g, hdec g⟩
  have hcomp : Measurable (Φh ∘ GroundTheory.Automorphic.HaarSK.mulMap P K) := by
    have e : Φh ∘ GroundTheory.Automorphic.HaarSK.mulMap P K = fun x : P × K => U ((x.1 : G) * x.2) * R x.2 := by
      funext x; exact hΦh_mul x.1 x.2
    rw [e]; exact (hU.comp hmm).mul (hRm.comp measurable_snd)
  have : PolishSpace P := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  have : PolishSpace K := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  have hΦhm : Measurable Φh := (hmm.measurable_comp_iff_of_surjective hsurj').mp hcomp
  set S : Set G := GroundTheory.Automorphic.HaarSK.mulMap P K '' (univ ×ˢ N) with hS
  have hpre : GroundTheory.Automorphic.HaarSK.mulMap P K ⁻¹' S = univ ×ˢ N := by
    ext ⟨p, k⟩
    constructor
    · rintro ⟨⟨p', k'⟩, ⟨-, hk'⟩, h⟩
      obtain ⟨m, hm, he⟩ := hdiff p' p k' k h
      refine ⟨trivial, ?_⟩
      show k ∈ N
      rw [he]; exact (hNinv m hm k').2 hk'
    · rintro ⟨-, hk⟩
      exact ⟨(p, k), ⟨trivial, hk⟩, rfl⟩
  have hSm : MeasurableSet S := by
    rw [← hmm.measurableSet_preimage_iff_of_surjective hsurj', hpre]
    exact MeasurableSet.univ.prod hN
  obtain ⟨c, hc⟩ := GlobalTheory.NAK.exists_eq_smul_map_mulMap_of_right P K μG (fun k _ => hright k) hP hK
    hsurj' μP μK
  have hS0 : μG S = 0 := by
    rw [hc, Measure.smul_apply, Measure.map_apply hmm hSm, hpre, Measure.prod_prod, hN0, mul_zero,
      smul_zero]
  have hsub : {g | ¬ Φ g = Φh g} ⊆ S := by
    intro g hg
    by_contra hgS
    apply hg
    have hg' := hdec g
    have hxN : (dec g).2 ∉ N := fun h => hgS ⟨dec g, ⟨trivial, h⟩, hg'⟩
    have e1 : Φ g = δ (dec g).1 * ψ (dec g).2 := by
      have := hφψ (dec g).2 hxN
      rw [← this, ← hΦ, hg']
    have e2 : Φh g = δ (dec g).1 * ψ (dec g).2 := by
      show U g * (ψ (dec g).2 / U (dec g).2) = _
      rw [show U g = δ (dec g).1 * U (dec g).2 by rw [← hUeq, hg'], mul_assoc, ENNReal.mul_div_cancel (hU0 _).1 (hU0 _).2]
    rw [e1, e2]
  exact ⟨Φh, hΦhm, ae_iff.2 (measure_mono_null hsub hS0)⟩

end GlobalTheory.EquivAEMeas
