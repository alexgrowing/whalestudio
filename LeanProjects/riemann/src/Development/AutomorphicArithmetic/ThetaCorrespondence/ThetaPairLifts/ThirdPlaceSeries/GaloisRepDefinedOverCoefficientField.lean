import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientFieldValuationFactsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvLgGFieldOfSmallField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.FieldAt
theorem galoisRep_field_of_definition_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  intro hP _ hL
  have h1 := _root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP
  have h2 := (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)
  refine (h1.inter h2).imp fun K _ _ _ _ hK => ?_
  obtain ⟨hF, hH, hV⟩ := hK
  refine hF.imp fun B f T hO hF' => ?_
  intro hKP w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨hX, -⟩ := hF' hKP T w Z
  have hHH := (hH (w.st Z) hO).1
  obtain ⟨hVs, hs⟩ := hV (w.st Z) hO
  have F := hX (GlobalTheory.TwInputs.JoinModel.realOf t hHH hVs hs) t.r.z.lev.C
  refine ⟨?_, F.roots, F.star⟩
  have v : ValLL0 (w.D Z) t.r.z.R.C := F.vals
  have e : t.r.z.R.C = TC.cf w.I w.l Z := t.r.z.lev.C
  rw [← e]
  exact v
end GlobalTheory.GalLoc.FieldAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valLL0_roots_of_unity_mem_star_closed_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  first | exact @_root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | exact _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt <;> assumption)
end
end
