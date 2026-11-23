import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterStatementAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeLocalCompatibleAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalLocalComponentAtSmallPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NOProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodRowCuspParamOfLiftStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.HeightCounting.Up
theorem conjDualParam_stable_of_prime_not_dividing_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := by
  intro hN hM hL
  have hlift := _root_.GlobalTheory.T.liftAll_of_parIn_of_mtInput hN hL
  have hloc := _root_.GlobalTheory.T.local_component_of_par_in_third_layer hN hL
  have hsz := GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices
  refine Step.trans (Step.and (Step.and (Step.and (Step.of_evLgG (KP := KPx) (p := fun _ _ _ _ => True) hlift)
    (Step.of_evLgG hloc)) (Step.of_evLgG hsz)) hM) (Step.of_all ?_)
  rintro K B f T - hKP - ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ w hS P x l
  obtain ⟨cp⟩ := hS.1
  obtain ⟨⟨M, ad, mt⟩⟩ := h4 w hS P x
  have hpar : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row := _root_.GlobalTheory.HeightCounting.Up.ParityConditions.ofSt l.a
  have hLift := h1 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
    M _ _ ad mt
  have hLoc := h2 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w x.o.Z
  have hLaws := _root_.UpperTheory.GalN.par_laws_bare hN hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row l.a.A.bare hpar
  have hconds := _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt hN.bc hN.what₂.bern hN.gen hN.std hL (Dof x) l.a.A.wdT l.a.A.au l.a.cg l.a.au
  exact _root_.GlobalTheory.T.cuspParam_of_definite_liftAll (Dof x) l.a.A.row hLaws hconds hEFK hCM hDef hLift hLoc
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parSt_of_third_layer_sMt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt <;> assumption)
end
end
