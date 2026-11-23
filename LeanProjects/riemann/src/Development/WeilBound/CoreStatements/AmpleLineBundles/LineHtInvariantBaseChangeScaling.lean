import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace CoverDenseAlt

theorem finsum_block {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']
    {J : Type} [Fintype J] (x : J → L) (hx : x ≠ 0) (c : L') (hc : c ≠ 0) :
    ∑ᶠ v : FinitePlace L', Real.log (⨆ i, v (c * algebraMap L L' (x i))) =
      -(∑ σ : L' →+* ℂ, Real.log ‖σ c‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (x i)) := by
  have hy : (fun i => algebraMap L L' (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    exact (map_eq_zero_iff _ (algebraMap L L').injective).1 (congrFun h i)
  have key : ∀ v : FinitePlace L', Real.log (⨆ i, v (c * algebraMap L L' (x i))) =
      Real.log (v c) + Real.log (⨆ i, v (algebraMap L L' (x i))) := by
    intro v
    have hvc : 0 < v c := FinitePlace.pos_iff.2 hc
    have h1 : (⨆ i, v (c * algebraMap L L' (x i))) = v c * ⨆ i, v (algebraMap L L' (x i)) := by
      rw [Real.mul_iSup_of_nonneg hvc.le]
      refine iSup_congr fun i => ?_
      exact map_mul v _ _
    rw [h1, Real.log_mul hvc.ne' (GroundTheory.Heights₂.Heights.iSup_place_pos hy v).ne']
  rw [finsum_congr key, finsum_add_distrib (SecLow.log_support_finite hc)
    (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite hy), SecLow.product_formula c hc,
    GroundTheory.Heights₂.Heights.finsum_log_iSup_algebraMap hx]

theorem lineHt_invariant_base_change_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  intro K _ ι _ A L _ _ L' _ _ e w c hw hc
  letI : Algebra L L' := e.toAlgebra
  haveI : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have hyk : ∀ k, (fun i => w ⟨k, i⟩) ≠ 0 := by
    intro k h
    obtain ⟨i, hi⟩ := hw k
    exact hi (congrFun h i)
  have hyk' : ∀ k, (fun i => c k * algebraMap L L' (w ⟨k, i⟩)) ≠ 0 := by
    intro k h
    obtain ⟨i, hi⟩ := hw k
    have h2 := congrFun h i
    simp only [Pi.zero_apply, mul_eq_zero, hc k, false_or] at h2
    exact hi ((map_eq_zero_iff _ (algebraMap L L').injective).1 h2)
  have fin' : (∑ᶠ v : FinitePlace L', ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (c k * e (w ⟨k, i⟩)))) =
      ∑ k, (A.a k : ℝ) * (-(∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩))) := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_finsum]
      congr 1
      exact finsum_block _ (hyk k) _ (hc k)
    · intro k _
      exact (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite (hyk' k)).subset
        (Function.support_mul_subset_right _ _)
  have finL : (∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      ∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [finsum_sum_comm]
    · exact Finset.sum_congr rfl fun k _ => (mul_finsum _ _).symm
    · intro k _
      exact (GroundTheory.Heights₂.Heights.support_log_iSup_place_finite (hyk k)).subset
        (Function.support_mul_subset_right _ _)
  have arch' : ∀ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p))) =
      ∑ k, (A.a k : ℝ) * Real.log ‖σ (c k)‖ +
        Real.log (A.h fun p => (σ.comp (algebraMap L L')) (w p)) := by
    intro σ
    have hσc : ∀ k, σ (c k) ≠ 0 := fun k => (map_ne_zero σ).2 (hc k)
    have hpos : 0 < A.h fun p => (σ.comp (algebraMap L L')) (w p) := by
      refine A.pos _ fun k => ?_
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero _).2 hi⟩
    have hs := A.smul (fun k => σ (c k)) (fun p => (σ.comp (algebraMap L L')) (w p)) hσc
    have hfun : (fun p : (Σ k, ι k) => σ (c p.1 * e (w p))) =
        fun p => σ (c p.1) * (σ.comp (algebraMap L L')) (w p) := by
      funext p
      rw [map_mul]
      rfl
    have hne : ∀ k ∈ Finset.univ, ‖σ (c k)‖ ^ A.a k ≠ 0 :=
      fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hσc k))
    rw [hfun, hs, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) hpos.ne', Real.log_prod hne]
    simp only [Real.log_zpow]
  have archSum : ∑ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p))) =
      ∑ k, (A.a k : ℝ) * ∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖ +
        Module.finrank L L' * ∑ τ : L →+* ℂ, Real.log (A.h fun p => τ (w p)) := by
    rw [Finset.sum_congr rfl fun σ _ => arch' σ, Finset.sum_add_distrib, Finset.sum_comm,
      GroundTheory.Heights₂.Heights.sum_embeddings_restrict (fun τ => Real.log (A.h fun p => τ (w p)))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hmul := Module.finrank_mul_finrank ℚ L L'
  have hpos' : 0 < Module.finrank ℚ L' := Module.finrank_pos
  have hposL : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hn : (Module.finrank L L' : ℝ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hmul
    omega
  have hnL : (Module.finrank ℚ L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hposL.ne'
  have hsplit : (∑ k, (A.a k : ℝ) * (-(∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)))) =
      -(∑ k, (A.a k : ℝ) * ∑ σ : L' →+* ℂ, Real.log ‖σ (c k)‖) +
        Module.finrank L L' * ∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  show (Module.finrank ℚ L' : ℝ)⁻¹ *
      ((∑ᶠ v : FinitePlace L', ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (c k * e (w ⟨k, i⟩)))) +
        ∑ σ : L' →+* ℂ, Real.log (A.h fun p => σ (c p.1 * e (w p)))) =
    (Module.finrank ℚ L : ℝ)⁻¹ *
      ((∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ τ : L →+* ℂ, Real.log (A.h fun p => τ (w p)))
  rw [fin', archSum, finL, hsplit, ← hmul]
  push_cast
  field_simp
  ring

end CoverDenseAlt
