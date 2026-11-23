import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MBlockParamH

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.InertialTypes
theorem main_alt_alt : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine _root_.GlobalTheory.TameType.inertialType_of_tame_m_alt _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact _root_.UpperTheory.One.M.split_param_of_typeBlock _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm
end GlobalTheory.InertialTypes
end
