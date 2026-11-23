import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveBoundOfSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundTransferOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsPreservedUnderLevelTransferOfCmDatum
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
theorem multiplicity_bound_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MoveToBase hL := by
  intro hP hS hL
  refine StepW.trans (StepW.and (_root_.GlobalTheory.T.levelI_same_gal_transfer_to_levelB1_list hP hS hL) (_root_.GlobalTheory.T.exists_levelB2_carried_of_levelB1 hP hS hL)) (StepW.of_all fun K B' f' T' w' _ _ h => ?_)
  obtain ⟨h, h'⟩ := h
  intro B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₁, ⟨l₁⟩, hC₁, hL₁⟩ := h B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₂, hl₂, hC₂, hL₂⟩ := h' P' x₁ (Dof x) l₁ hC₁
  exact ⟨x₂, hl₂, hC₂, fun c hc => hL₂ c (hL₁ c hc)⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveToBase_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MoveToBase hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt | exact _root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt <;> assumption)
end
end
