import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesTuplePlacesOverFixedCharacterPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFockPolynomialsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentifiedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove

theorem realMove_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x' g' hg' a') ι) :=
  fun x x' ι e g g' l hg hg' a a' =>
    let ⟨eK, γ, h1, h2⟩ := GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq x x' ι e g g' l hg hg' a a'
    realMove_of_parts (GlobalTheory.T.linkedStates_frames_lattices_models_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.linked_construction_states_characters_agree x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_finiteGroups_levels_correspond x x' ι e g g' l hg hg' a a' γ h2) (GlobalTheory.T.linkedStates_tuplePlaces_over_fixedCharacterPrime x x' ι e g g' l hg hg' a a')
      (GlobalTheory.T.linkedStates_fockPolynomials_agree x x' ι e g g' l hg hg' a a') (GlobalTheory.T.rationalForms_linkedConstructionStates_identified x x' ι e g g' l hg hg' a a' eK γ h1 h2)

end GlobalTheory.HeightCounting.SerMove
