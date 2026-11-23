import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocMapOfMem
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

theorem GlobalTheory.shortRadius_of_fixes_zero_section : ∀ (d : ℕ) (C U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (q : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d → ℝ), IsCompact C → IsOpen U → C ⊆ U → Continuous f → (∀ z ∈ C, f (z, 0) = z) → ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => q x.1 x.2) (C ×ˢ Set.univ) → (∀ z ∈ C, ∀ (t : ℝ) η, q z (t • η) = t ^ 2 * q z η) → (∀ z ∈ C, ∀ η, η ≠ 0 → 0 < q z η) → ∃ ε, 0 < ε ∧ ∀ z ∈ C, ∀ η, q z η < ε → f (z, η) ∈ U := by
  intro d C U f q hC hU hCU hf hf0 hq hhom hpos
  have hK : IsCompact (C ×ˢ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1) :=
    hC.prod (isCompact_sphere 0 1)
  have hqK : ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => q x.1 x.2)
      (C ×ˢ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1) :=
    hq.mono (Set.prod_mono le_rfl (Set.subset_univ _))
  obtain ⟨m, hm0, hm⟩ := hK.exists_forall_le' hqK (a := 0) (by
    rintro ⟨z, u⟩ ⟨hz, hu⟩
    have hu1 : ‖u‖ = 1 := by simpa using hu
    exact hpos z hz u (by rintro rfl; simp at hu1))
  have hC0 : IsCompact (C ×ˢ ({0} : Set (ReciprocityTheory.L2DbarEstimates.V d))) := hC.prod isCompact_singleton
  have hsub : C ×ˢ ({0} : Set (ReciprocityTheory.L2DbarEstimates.V d)) ⊆ f ⁻¹' U := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simpa [hf0 z hz] using hCU hz
  obtain ⟨δ, hδ0, hδ⟩ := hC0.exists_thickening_subset_open (hU.preimage hf) hsub
  refine ⟨m * δ ^ 2, by positivity, ?_⟩
  intro z hz η hη
  by_cases h0 : η = 0
  · subst h0; rw [hf0 z hz]; exact hCU hz
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr h0
  have hu : ‖η‖⁻¹ • η ∈ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hmu := hm (z, ‖η‖⁻¹ • η) ⟨hz, hu⟩
  have heq : q z η = ‖η‖ ^ 2 * q z (‖η‖⁻¹ • η) := by
    rw [← hhom z hz, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hlt : ‖η‖ ^ 2 < δ ^ 2 := by
    have h1 : m * ‖η‖ ^ 2 ≤ q z η := by
      rw [heq]; simp only at hmu; nlinarith [sq_nonneg ‖η‖]
    have : m * ‖η‖ ^ 2 < m * δ ^ 2 := lt_of_le_of_lt h1 hη
    exact lt_of_mul_lt_mul_left this hm0.le
  have hnδ : ‖η‖ < δ := lt_of_pow_lt_pow_left₀ 2 hδ0.le hlt
  have hmem : (z, η) ∈ Metric.thickening δ (C ×ˢ ({0} : Set (ReciprocityTheory.L2DbarEstimates.V d))) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(z, 0), ⟨hz, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, dist_zero_right]
    simpa using hnδ
  exact hδ hmem
