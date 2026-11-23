import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_forms_exist

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type}

theorem shift (x : (Σ k, ι k) → Ω) (t : ∀ k, ι k) (e : K → ℕ) {F : MRing ι O} {d : K → ℕ}
    (hF : IsMultiHomog F d) :
    ∃ G : MRing ι O, IsMultiHomog G (d + e) ∧ aeval x G = aeval x F * ∏ k, x ⟨k, t k⟩ ^ e k := by
  have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
    (fun k => (X ⟨k, t k⟩ : MRing ι O) ^ e k) (fun k => e k • blockWeight ι ⟨k, t k⟩)
    (w := blockWeight ι)
    (fun k _ => (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, t k⟩).pow (e k))
  have he : ∑ k, e k • blockWeight ι ⟨k, t k⟩ = e := by
    ext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  refine ⟨F * ∏ k, (X ⟨k, t k⟩ : MRing ι O) ^ e k, IsWeightedHomogeneous.mul hF h, ?_⟩
  simp [map_prod]

def fracs (O : Type) [CommRing O] [Algebra O Ω] (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) : Subalgebra O Ω where
  carrier := {v | ∃ (d : K → ℕ) (F : MRing ι O), IsMultiHomog F d ∧ aeval x F = v * ∏ k, x ⟨k, s k⟩ ^ d k}
  mul_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    refine ⟨d + e, F * G, IsWeightedHomogeneous.mul hF hG, ?_⟩
    simp only [map_mul, eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  add_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    obtain ⟨F', hF', eF'⟩ := shift x s e hF
    obtain ⟨G', hG', eG'⟩ := shift x s d hG
    rw [add_comm e d] at hG'
    refine ⟨d + e, F' + G', IsWeightedHomogeneous.add hF' hG', ?_⟩
    simp only [map_add, eF', eG', eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  algebraMap_mem' r := ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩

theorem chartRing_le_fracs (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (hs : mseg x s ≠ 0) :
    chartRing O (mseg x) s ≤ fracs O x s := by
  unfold chartRing
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  refine ⟨fun _ => 1, ∏ k, (X ⟨k, j k⟩ : MRing ι O), ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
      (fun k => (X ⟨k, j k⟩ : MRing ι O)) (fun k => blockWeight ι ⟨k, j k⟩)
      (w := blockWeight ι) (fun k _ => isWeightedHomogeneous_X O (blockWeight ι) ⟨k, j k⟩)
    have he : ∑ k, blockWeight ι ⟨k, j k⟩ = fun _ => 1 := by
      ext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [he] at h
    exact h
  · simp only [map_prod, aeval_X, pow_one]
    have hm : ∏ k, x ⟨k, s k⟩ = mseg x s := rfl
    rw [hm, div_mul_cancel₀ _ hs]
    try rfl

end PositivityTheory.Xgn.A_forms_exist
