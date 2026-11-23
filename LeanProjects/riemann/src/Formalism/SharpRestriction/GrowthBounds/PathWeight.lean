import Formalism.SharpRestriction.GrowthBounds.PathWeight.Lemma4OfRemainingStatements
import Formalism.SharpRestriction.GrowthBounds.PathWeight.MdWeightMapDomain
import Formalism.SharpRestriction.GrowthBounds.PathWeight.CoeUntopDLeAlt
import Formalism.SharpRestriction.GrowthBounds.PathWeight.LetterWeightPos
import Formalism.SharpRestriction.GrowthBounds.PathWeight.DvDegOtherMono
import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeOldest
import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure
import Formalism.SharpRestriction.GrowthBounds.PathWeight.SymbolGeneratorData

noncomputable section

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem classMap_estimate_of_admissible : ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, StandardMonomialSpanBis D → PathPairCorrespondence D → admB2 D → admB3 D → CoefficientValuationLemma D → LargePrimeLengthVanishing D →
    Conclusion6 D C (C + 1) C := by
  by_cases hE : FieldMultidegreeDivisibility
  · obtain ⟨C, hC, hD⟩ := restDivM hE
    exact ⟨C, hC, fun D hA3 hB1 hB2 hB3 hC1 _ => lemma4_of_remaining_statements D C (C + 1) C restModel (hD restGeom)
      (generator_pair_conditions_of_admitted D hA3 hB1) (generator_path_homogeneous_holds D hB2 hB3 hC1) (restMon D) restPh⟩
  · exact ⟨1, le_rfl, fun D _ _ _ _ _ h => absurd h hE⟩

theorem export_bound_of_admissible : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), admitted D CLa Ck Crk Cdeg →
    aux₃ D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := classMap_estimate_of_admissible
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hA3, hB1, hB2, hB3, _, hC1, hE, _⟩ := hA
  exact ⟨theta_kernel_expansion D, splitting_package_holds D, segment_statement_holds D, order_lemma_holds D, divisibility_of_field_lemma D hE,
    H D hA3 hB1 hB2 hB3 hC1 hE⟩

theorem stmtE_proved (D : Formalism.BasicNotions.D7) : ClosedFormOfAdmitted D := by
  obtain ⟨C, hC, H⟩ := export_bound_of_admissible
  intro CLa Ck Crk Cdeg hA
  exact ⟨C, C + 1, C, by linarith, by linarith, by linarith, H D CLa Ck Crk Cdeg hA⟩

theorem stmtEF_proved {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyClosedForm Fm := by
  obtain ⟨C, hC, H⟩ := export_bound_of_admissible
  intro CLa Ck Crk Cdeg hA
  exact ⟨C, C + 1, C, by linarith, by linarith, by linarith, 0, fun x _ i => H _ CLa Ck Crk Cdeg (hA x i)⟩

theorem stmtEDF_proved (Fm : Formalism.MainNotions.DFamP) : DerivativeStatementClosedDesign Fm := by
  obtain ⟨C, hC, H⟩ := export_bound_of_admissible
  intro CLa Ck Crk Cdeg hA
  exact ⟨C, C + 1, C, by linarith, by linarith, by linarith,
    fun ε h0 h1 => ⟨0, fun x _ i => H _ CLa Ck Crk Cdeg (hA ε h0 h1 x i)⟩⟩

end Formalism.MainNotions.G.symbolGeneratorData
