import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllTriplesLocalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemTripleLayerInputs
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end GlobalTheory.RowTriple
namespace GlobalTheory.RowTriple
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal
theorem forall_triple_condition_of_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt hP hS hL) fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨cf, Rw, low, Pq, S, hL', eig, θ, Bs, Sb, hSb, hKs, hT, hOcc, hcp, hall, hloc, hR⟩ := h
  exact GlobalTheory.TwistedSelmerCompare.allTriples_of_tripAll _
    (tripAll_of_sideB _ cf Rw low Pq S hL' eig θ Bs Sb hSb hKs hT hOcc hcp hall hloc hR)
end GlobalTheory.RowTriple
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allTriples_at_members_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  first | exact @_root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt | exact _root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt <;> assumption)
end
end
