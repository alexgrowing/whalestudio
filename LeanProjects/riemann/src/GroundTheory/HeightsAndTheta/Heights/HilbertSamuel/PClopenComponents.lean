import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIrreducibleConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem vanishingIdeal_zeroLocus_diff_of_nonempty {σ : Type} [Fintype σ]
    (W J : Ideal (MvPolynomial σ ℂ)) [hW : W.IsPrime]
    (hne : (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty) :
    vanishingIdeal ℂ (zeroLocus ℂ W \ zeroLocus ℂ J) = W := by
  refine le_antisymm ?_ ?_
  · intro f hf
    obtain ⟨z₀, hz₀W, hz₀J⟩ := hne
    simp only [mem_zeroLocus_iff, not_forall] at hz₀J
    obtain ⟨g, hgJ, hg⟩ := hz₀J
    have hgW : g ∉ W := fun h => hg (hz₀W g h)
    have hfg : f * g ∈ W := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W, mem_vanishingIdeal_iff]
      intro z hz
      by_cases hzJ : z ∈ zeroLocus ℂ J
      · rw [map_mul, hzJ g hgJ, mul_zero]
      · rw [map_mul, (mem_vanishingIdeal_iff.mp hf) z ⟨hz, hzJ⟩, zero_mul]
    exact (hW.mem_or_mem hfg).resolve_right hgW
  · calc W ≤ vanishingIdeal ℂ (zeroLocus ℂ W) := le_vanishingIdeal_zeroLocus W
      _ ≤ _ := vanishingIdeal_anti_mono Set.sdiff_subset

variable (ι) in

def multiIrrelevantIdeal : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun i : (∀ k, ι k) => ∏ k, (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))

omit [∀ k, Fintype (ι k)] in

theorem not_mem_zeroLocus_multiIrrelevantIdeal (z : (Σ k, ι k) → ℂ) :
    z ∉ zeroLocus ℂ (multiIrrelevantIdeal ι) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  rw [multiIrrelevantIdeal, zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, not_forall, map_prod, aeval_X]
  constructor
  · rintro ⟨i, hi⟩ k
    exact ⟨i k, fun h => hi (Finset.prod_eq_zero (Finset.mem_univ k) h)⟩
  · intro h
    choose i hi using h
    exact ⟨i, Finset.prod_ne_zero_iff.mpr fun k _ => hi k⟩

omit [∀ k, Fintype (ι k)] in

theorem mcPts_eq_zeroLocus_diff (P : Ideal (MRing ι)) :
    mcPts P = zeroLocus ℂ (P.map (MvPolynomial.map (Int.castRingHom ℂ))) \
      zeroLocus ℂ (multiIrrelevantIdeal ι) := by
  ext z
  rw [Set.mem_sdiff, not_mem_zeroLocus_multiIrrelevantIdeal]
  simp only [mcPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨fun p hp => ?_, hb⟩
    have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hv f hf
    have h0 := RingHom.mem_ker.mp (hle hp)
    exact h0
  · rintro ⟨hz, hb⟩
    refine ⟨hb, fun f hf => ?_⟩
    have := hz _ (Ideal.mem_map_of_mem _ hf)
    exact this

theorem ClopenComponents.proof (h : IrreducibleConnected.Statement) : ClopenComponents.Statement := by
  classical
  intro K _ _ ι _ P e A _ hAsub hA
  set PC := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  set J := multiIrrelevantIdeal ι with hJ
  have hmc : mcPts P = zeroLocus ℂ PC \ zeroLocus ℂ J := mcPts_eq_zeroLocus_diff P
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ PC
  let S := hfin.toFinset.filter fun W =>
    (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧ zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A
  have hS : ∀ W ∈ S, W ∈ PC.minimalPrimes ∧ (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧
      zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A := by
    intro W hW
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    exact hW
  have hcover : ∀ z ∈ A, ∃ W ∈ S, z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := by
    intro z hz
    have hzm : z ∈ mcPts P := hAsub hz
    rw [hmc] at hzm
    obtain ⟨hzPC, hzJ⟩ := hzm
    have hker : PC ≤ RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ) :=
      fun p hp => RingHom.mem_ker.mpr (hzPC p hp)
    have : (RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le hker
    have hzW : z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := ⟨fun p hp => RingHom.mem_ker.mp (hWle hp), hzJ⟩
    have hsub : zeroLocus ℂ W \ zeroLocus ℂ J ⊆ mcPts P := by
      rw [hmc]
      exact Set.sdiff_subset_sdiff_left (zeroLocus_anti_mono hWmin.1.2)
    have hpc : IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J) := h _ W J hWmin.1.1
    have hpc' : IsPreconnected (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' (zeroLocus ℂ W \ zeroLocus ℂ J)) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr hsub]
      exact hpc
    have hin := hpc'.subset_isClopen hA ⟨⟨z, hsub hzW⟩, hzW, hz⟩
    refine ⟨W, ?_, hzW⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hWmin, ⟨z, hzW⟩, fun y hy => hin (show (⟨y, hsub hy⟩ : mcPts P) ∈ _ from hy)⟩
  have hAU : A = ⋃ W ∈ S, (zeroLocus ℂ W \ zeroLocus ℂ J) := by
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun hz => hcover z hz, fun ⟨W, hW, hz⟩ => (hS W hW).2.2 hz⟩
  refine ⟨S, fun W hW => (hS W hW).1, ?_, ?_⟩
  · ext z
    rw [hAU, hmc]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨W, hW, hzW, hzJ⟩
      exact ⟨⟨fun p hp => hzW p ((hS W hW).1.1.2 hp), hzJ⟩, W, hW, hzW⟩
    · rintro ⟨⟨_, hzJ⟩, W, hW, hzW⟩
      exact ⟨W, hW, hzW, hzJ⟩
  · rw [hAU]
    ext f
    rw [mem_vanishingIdeal_iff]
    simp only [Submodule.mem_iInf]
    constructor
    · intro hf W hW
      have : W.IsPrime := (hS W hW).1.1.1
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff]
      exact fun x hx => hf x (Set.mem_biUnion hW hx)
    · intro hf x hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
      have : W.IsPrime := (hS W hW).1.1.1
      have hfW := hf W hW
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff] at hfW
      exact hfW x hxW

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
