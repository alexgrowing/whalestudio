import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionCanonicalWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesSectionQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombSectionsNeZeroOnFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtlasSectionsMulDivNonvanishingIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseNonvanishingSetOfNeZeroOnComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDisjointMeetsComponentsStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_etale_frame_of_finite_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (A.zeroSet s).Finite → ∃ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn hH E L s hs hS
  obtain ⟨H, hH⟩ := hH
  obtain ⟨T, hTf, hTd, hTm⟩ := GlobalTheory.T.exists_finite_disjoint_meeting_every_component n Y ι La A hn _ hS
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset n Y ι La A H hH hTf.toFinset (A.kap + E)
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos n Y ι La A H ((2 * n + 4) • A.kap + E + L) hH
  obtain ⟨t0, t, a, ht0, ht, ha, hT⟩ := hk1 (max k1 k2) (le_max_left _ _)
  obtain ⟨J, hJ, hJeq⟩ := GlobalTheory.T.exists_jacobian_section_canonical_weight n Y ι La A (A.kap + (max k1 k2) • H) t0 t ht0 ht
  obtain ⟨s', hs', hs'T, C, hC, hs'C⟩ := GlobalTheory.T.exists_linComb_sections_ne_zero_on_finset n Y ι La A L n s hTf.toFinset hs (by
    intro P hP hPS
    exact Set.disjoint_left.mp hTd (hTf.mem_toFinset.mp hP) hPS)
  obtain ⟨hmul, hopen, hfrac⟩ := GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen n Y ι La A
  have ha' : A.IsSec ((A.kap + (max k1 k2) • H) + (A.kap + E)) a := by
    have e : (A.kap + (max k1 k2) • H) + (A.kap + E) = A.kap + ((A.kap + E) + (max k1 k2) • H) := by
      abel
    rw [e]; exact ha
  obtain ⟨h1, h1n⟩ := hmul _ _ _ _ ht0 hJ
  obtain ⟨h2, h2n⟩ := hmul _ _ _ _ h1 ha'
  obtain ⟨h3, h3n⟩ := hmul _ _ _ _ h2 hs'
  have hdec : ∀ y, t0 (A.pick y) y * J (A.pick y) y * a (A.pick y) y * s' (A.pick y) y ≠ 0 →
      t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y ∧ a (A.pick y) y ≠ 0 := by
    intro y hy
    have hJ0 : J (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ht00 : t0 (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ha0 : a (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    refine ⟨ht00, ?_, ha0⟩
    rw [hJeq (A.pick y) y (A.mem_pick y) ht00] at hJ0
    exact right_ne_zero_of_mul hJ0
  have hopen' := hopen _ _ h3
  obtain ⟨M, hM⟩ := (isCompact_range (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_nsq A h2)).bddAbove
  refine ⟨_, fun i y => t0 i y * J i y * a i y * s' i y, A.zmap t0 t, fun i y => a i y / t0 i y,
    h3, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (A.kap + (max k1 k2) • H) + (A.kap + (2 * n) • (A.kap + (max k1 k2) • H)) +
        ((A.kap + (max k1 k2) • H) + (A.kap + E)) + L
        = ((2 * n + 4) • A.kap + E + L) + ((2 * n + 2) * max k1 k2) • H := by
      module
    rw [e]
    apply hk2
    calc k2 ≤ max k1 k2 := le_max_right _ _
      _ ≤ (2 * n + 2) * max k1 k2 := Nat.le_mul_of_pos_left _ (by omega)
  · exact GlobalTheory.T.isEtaleCoordinates_section_quotients n Y ι La A _ t0 t _ ht0 ht hopen' (fun y hy => ⟨(hdec y hy).1, (hdec y hy).2.1⟩)
  · exact hfrac _ _ a t0 _ ha' ht0 (fun y hy => ⟨(hdec y hy).2.2, (hdec y hy).1⟩)
  · refine GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components n Y ι La A _ _ T h3 hTm ?_
    intro P hP
    obtain ⟨ht0P, hcP, haP⟩ := hT P (hTf.mem_toFinset.mpr hP)
    have hsP := hs'T P (hTf.mem_toFinset.mpr hP)
    have hJP : J (A.pick P) P ≠ 0 := by
      rw [hJeq (A.pick P) P (A.mem_pick P) ht0P]
      exact mul_ne_zero (pow_ne_zero _ ht0P) hcP
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht0P hJP) haP) hsP
  · refine ⟨max M 1 * C, by positivity, fun y => ?_⟩
    rw [h3n y, mul_assoc]
    exact mul_le_mul ((hM ⟨y, rfl⟩).trans (le_max_left _ _)) (hs'C y)
      (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_nonneg A _ _ _) (by positivity)

end GlobalTheory
