import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrobeniusReductionProduct
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WordOrderBoundOfNumericBound
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LateVectorsDistinctTops

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem discriminant_nonzero_mod_uniformiser : DiscriminantNonzeroModUniformiser := discriminant_nonzero_of_injective_tops late_vectors_distinct_tops

theorem generator_modulo_uniformiser_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hC : 32 ≤ C₀) : GeneratorModuloUniformiser C₀ := by
  have hV1 : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D := hAdm.2.2.2.2.2.2.2.1.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  have hB12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have h41b : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments
  have hW3 := column_conditions_of_numeric_bounds D hV1 hA3 C₀ late_row_injective ell_degree_le_power_bound (power_exceeds_max_multiplicity C₀) (threshold_power_bound_of_counts C₀ h41b oldest_letter_in_segment)
  have hW4 := word_order_bound_of_numeric_bound D hA3 C₀ late_row_injective (order_numeric_bound_of_oldest C₀ oldest_letter_in_segment)
  have hW2 := allowed_letters_of_late_rows D hA3 C₀ late_row_injective
  have hWord := column_word_reduction_of_four D hB12 C₀ (frobenius_reduction_product C₀) hW2 hW3 hW4
  exact generator_of_segment_reductions C₀ coarse_label_factorisation top_degree_comparison discriminant_multihomogeneous (discriminant_ne_zero_of_residue_ne_zero discriminant_nonzero_mod_uniformiser) h41b (segment_reduction_of_column_words D hB12 C₀ hWord)
    segment_image_multihomogeneous segment_product_degree_determined

theorem top_count_lower_bounds (C₀ : ℝ) (hC : 32 ≤ C₀) : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments

end Formalism.MainNotions.SelectionLemmas.Pf
