import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharWSeedStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLargeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLawsAtStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

open Formalism.L2.Pj GlobalTheory.AtMember

namespace GlobalTheory.Mem.R3.Rw

theorem selHalf_of_pin {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (p : ColPin w) : SelHalf w.I := by
  intro a b P hP P' hP' hq
  obtain ⟨q, hq, hqP, hqP'⟩ := hq
  obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
  obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
  have hab : ∀ v, (w.I.sel v).under (𝓞 B.host.F) = v := fun v => by
    have h := p.above v
    unfold Formalism.L2.Host.aboveF at h
    rw [Set.Finite.mem_toFinset] at h
    exact h
  have hmem : ∀ v, ((q : 𝓞 B.host.E) ∈ (w.I.sel v).asIdeal) → (q : 𝓞 B.host.F) ∈ v.asIdeal := fun v h => by
    rw [← hab v]
    show (q : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal.comap (algebraMap _ _)
    rw [Ideal.mem_comap, map_natCast]
    exact h
  have := p.half v v' q hq (hmem v hqP) (hmem v' hqP')
  exact congrArg HeightOneSpectrum.asIdeal this

theorem isIdG_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl

set_option maxHeartbeats 4000000 in

theorem datExS_evLg (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.CasselmanWallach) (h5 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h6 : GlobalTheory.Published.DiscreteSeriesExists)
    (h7 : GlobalTheory.Published.HarishChandraFinite) :
    EvLg fun K B f T => ∀ w : ColW B f T, Pinned K B f T w → ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f →
      R3.GrpAt (w.st Z) w.I → Formalism.L2.Theta.VolTieG (w.D Z) →
      ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
    (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.T.eventually_definiteSpaces_standard_and_large GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))
  rintro K ⟨hK, hKC, hO⟩
  refine hO.imp ?_
  rintro B f T hOv hOB w ⟨pin⟩ Z hX _ hgrp hVol
  set X : Stages := w.st Z with hXd
  set I := w.I with hId
  set Wt : Set B.places.Pl := {v | B.places.resChar v ∈ T.pl} with hWt
  obtain ⟨hHH, -, -, hPos, hStd, hX', -, -⟩ := hK X hOv
  obtain ⟨hVS, hnV⟩ := hKC X hOv
  have hok := w.ok
  have hC := w.C_eq
  have hrange := w.xi_range
  have hsel : SelHalf I := selHalf_of_pin pin
  have hfin : Wt.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B T.pl
  have hconj : ∀ v ∈ Wt, B.places.conj v ∈ Wt :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f ≤ B.KsC := (GlobalTheory.Mem.Base.KsExact.lower w.exact).2.2.1
  have hval : Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) := w.val _ _ _ _ _ _
  obtain ⟨C, alg, hPin, hCe, hCL, hCK, hCE, hLJ, hAT, hVal, hmu⟩ := GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one X f hch hval hVol
  have hLC := hPin.laws
  have hpb := hPin.pb
  obtain ⟨hVals, hOk3⟩ := hOB w.px I hX hok hC hrange
  have hrange' : Set.range I.xi = T.set I.C := by rw [hC]; exact hrange
  obtain ⟨Xg, tr₀, R₀, cG, hLev, hIdG, hGood, hMu, hIdem, hPre0, hIn, hTup, hAll, hKeep, hBrg⟩ :=
    GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices X w.px I hX T Wt C.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hX' hPos hCK hCE
      (fun L hL hLC' => hmu _ L _ hL (hLC'.trans (by rw [hC])))
  have hValR : Formalism.L2.Host.ValLL X.toD7 R₀.C := by rw [hLev.C, hC]; exact hVal
  have hpbR : C.pb = R₀.C.P.pb := by rw [hLev.C, hC]; exact hpb
  have hExAt : ∀ R : RealDat X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀).A C.Q.c.F,
      R.Pre1 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt :=
    fun R hP hc ht _ _ => GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 X.toD7 _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht
  have hfinT : Finite (TupU I (usedOf I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))).1 ∨ τ ∈ tuOf I (usedOf I T Wt)} : Set _).Finite :=
      (Set.finite_singleton _).union (tuOf I (usedOf I T Wt)).finite_toSet
    exact hs.to_subtype
  have hGeoEx := GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne h3 X.toD7 _ _ _ _ _ C (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 hVol hLJ hLC hAT
    hfinT hVS hnV
  obtain ⟨tr, dict, mu, chiW, x₀, cE, R, cG', hPins, hEx, hLevEq, hEG, hCG, -, hmuEq, htw, hBrgI, hGeo⟩ :=
    GlobalTheory.StandardWeightCharacter.charW_seed_std X w.px I hX (usedOf I T Wt) Xg tr₀ C R₀ cG (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 X.toD7) hIdem hExAt hGeoEx
      hValR hpbR hPre0 hIn hTup hAll hKeep
  have hPg : R.Pg = R₀.Pg := congrArg LevCh.Pg hLevEq
  have hRC : R.C = R₀.C := congrArg LevCh.C hLevEq
  have hgood : GoodSet X (px := w.px) (R.eG.trans cG') Xg := by
    rw [trans_eq_of_heq' X R.eG R₀.eG cG' cG hPg hEG hCG]; exact hGood
  let z : Dat X I hX T Wt :=
    { Xg := Xg, tr := tr, core := GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE,
      alg := inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL), alg_eq := hCe, R := R, cG := cG', geo := hGeo.some,
      pins := hPins, lev := by rw [hLevEq]; exact hLev, idG := isIdG_of_heq' X R.eG R₀.eG hPg hEG hIdG, good := hgood,
      mu := by rw [hmuEq, htw]; exact hMu, fieldValues_mem_fixedField := hCL, Ks_le := hCK }
  have hch' := hPins.char
  have hPre : GlobalTheory.RealGeo.PreChar R.toRealDat :=
    ⟨hch'.base.lev, hch'.base.grp.red_R, hch'.base.grp.red_L, hch'.base.grp.record, hch'.base.fam, hch'.base.models,
      RealDat.chain_of_weak hch'.base.chain hEx, RealDat.thP_of_weak hch'.base.thP hEx⟩
  have hP : CorePin (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE).toCore (Fr.at X f).P.pb :=
    hPin.reCore hGeo.some.fw.laws.toLawsM
  refine ⟨z, hEx, ?_, ⟨hP.laws, hP.canon, hP.rank, hP.pb⟩, hBrgI hBrg⟩
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral h3 X.toD7 _ _ _ _ (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) R.toRealDat
    (fun _ => 1) hGeo.some hPre hch'.base.grp.chiW (by show C.pb = _; rw [hRC]; exact hpbR) hnV).1

theorem datExS_of_harishChandra_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → DatExS :=
  fun h1 h2 h3 h4 h5 h6 h7 =>
    GlobalTheory.Mem.Top.GroupRetwisting.Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg (datExS_evLg h1 h2 h3 h4 h5 h6 h7))

end GlobalTheory.Mem.R3.Rw

end
