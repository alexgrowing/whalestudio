import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightReal

open MeasureTheory Matrix Set Filter Ad3 Ad3.K Ad3.K.LC

namespace GlobalTheory.CompanionTheory.DualZetaC

theorem range_units_val : Set.range (Units.val : ℂˣ → ℂ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro h
    exact ⟨Units.mk0 x h, rfl⟩

theorem measurableEmbedding_units_val : MeasurableEmbedding (Units.val : ℂˣ → ℂ) := by
  refine ⟨Units.val_injective, comap_measurable _, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [Set.image_preimage_eq_inter_range, range_units_val]
  exact ht.inter (measurableSet_singleton 0).compl

theorem map_val_mulC : Measure.map (Units.val : ℂˣ → ℂ) mulC =
    volume.withDensity fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹ := by
  rw [mulC, measurableEmbedding_units_val.map_comap, range_units_val]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  exact compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))

instance sigmaFinite_mulC : SigmaFinite mulC := by
  have h : SigmaFinite (Measure.map (Units.val : ℂˣ → ℂ) mulC) := by
    rw [map_val_mulC]
    exact SigmaFinite.withDensity_of_ne_top (ae_of_all _ fun x => ENNReal.ofReal_ne_top)
  exact SigmaFinite.of_map _ measurableEmbedding_units_val.measurable.aemeasurable h

end GlobalTheory.CompanionTheory.DualZetaC
