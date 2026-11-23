import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmptyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem parSt_of_prN_sMt : PrN → SMt → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ParSt hL := by
  intro hN hM hL
  have hlift := GlobalTheory.T.lift_all_of_inputs hN hL
  have hloc := GlobalTheory.T.row_local_all hN hL
  have hsz := GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices
  refine Step.trans (Step.and (Step.and (Step.and (Step.of_evLgG (KP := KPx) (p := fun _ _ _ _ => True) hlift)
    (Step.of_evLgG hloc)) (Step.of_evLgG hsz)) hM) (Step.of_all ?_)
  rintro K B f T - hKP - ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ w hS P x l
  obtain ⟨cp⟩ := hS.1
  obtain ⟨⟨M, ad, mt⟩⟩ := h4 w hS P x
  have hpar : ParIn hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row := ParIn.ofSt l.a
  have hLift := h1 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
    M _ _ ad mt
  have hLoc := h2 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w x.o.Z
  have hLaws := GlobalTheory.T.parameter_laws_empty hN hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row l.a.A.bare hpar
  have hconds := GlobalTheory.T.base_change_of_hypotheses hN.bc hN.what₂.bern hN.ds hN.gen hN.std hL (Dof x) l.a.A.wdT l.a.A.au l.a.cg l.a.au
  exact GlobalTheory.T.good_row_cusp_param (Dof x) l.a.A.row hLaws hconds hEFK hCM hDef hLift hLoc

end GlobalTheory.HeightCounting.Up
