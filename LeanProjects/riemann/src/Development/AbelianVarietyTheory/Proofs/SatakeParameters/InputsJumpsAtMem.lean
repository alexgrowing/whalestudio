import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesLocationOfMembershipStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm8AndLambdaUsedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedRealizationPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement

noncomputable section

namespace GlobalTheory.NRows.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem atMem_of_evLgG {hL : GlobalTheory.Published.LocalLanglandsGL} {P : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} {p q : LayP hL}
    (hP : EvLgG P) (h : AtMem hL p)
    (hpq : ∀ K B f T, P K B f T → KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c) →
      Nonempty (RXs t) → ColPin w → p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp (EvG.inter hP h) fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T H.1 kp w Z Wt p0 t nch n xd c a b d (H.2 kp w Z Wt p0 t nch n xd c a b d)

theorem inputs_jumps_atMem : PrN → GlobalTheory.NRows.HypothesesX → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ c => ∃ I : GlobalTheory.NRows.Inputs hL (w.D Z), PinAt c.a I.P ∧ JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro prn prx hL
  have hA := GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.exists_tied_realization_place prn hL) (GlobalTheory.T.series_location_of_membership prn hL)) (GlobalTheory.HeightCounting.JumpsAt.jumpsCard_atMem prx.ht hL)
  refine atMem_of_evLgG (EvG.imp (EvG.inter GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices (GlobalTheory.T.adm8_and_lamUsed_of_parameterChoice prn prx)) fun _ _ _ _ _ hK => large₂.inter hK.1 hK.2) hA ?_
  rintro K B f T ⟨hS, hR⟩ kp w Z Wt p0 t nch n xd c ⟨ne⟩ _ cp ⟨⟨⟨X, hpin, -⟩, ser⟩, jumps⟩
  obtain ⟨-, -, -, -, -, hdef, -⟩ := hS kp T w Z
  have hr := hR kp w cp Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt t.r.Z X.X.given.params
  exact ⟨⟨X, { hypO := ne.large.1
               c1 := GlobalTheory.DesignBC.jointCond_of_definite _ hdef
               bc := GlobalTheory.T.base_change_of_hypotheses prn.bc prn.what₂.bern prn.ds prn.gen prn.std hL _ X.P.T X.P.H.au X.P.cg X.P.au
               lam := hr.2
               isot := hr.1
               ser := ser
               typeNZ := GlobalTheory.T.type_nonzero_of_howe_unramified prn.decay prn.howe prx _ _ _ _ X.X }⟩, hpin, jumps⟩

end GlobalTheory.NRows.AtLayer

end
