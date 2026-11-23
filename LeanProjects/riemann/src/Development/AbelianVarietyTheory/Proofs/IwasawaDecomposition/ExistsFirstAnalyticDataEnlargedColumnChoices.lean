import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem seed_at_enl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ hgrp _ core' alg' _ _ hKs _ _ _ _ _

  set Wt' : Set B'.places.Pl := {v | B'.places.resChar v ∈ T'.pl} with hWt
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  have hok := w'.ok
  have hC := w'.C_eq
  have hrange := w'.xi_range
  have hsel : SelHalf w'.I := by
    intro a b P hP P' hP' hq
    obtain ⟨q, hq, hqP, hqP'⟩ := hq
    obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
    obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
    have hab : ∀ v, (w'.I.sel v).under (𝓞 B'.host.F) = v := fun v => by
      have h := pin.above v
      unfold Formalism.L2.Host.aboveF at h
      rw [Set.Finite.mem_toFinset] at h
      exact h
    have hmem : ∀ v, ((q : 𝓞 B'.host.E) ∈ (w'.I.sel v).asIdeal) → (q : 𝓞 B'.host.F) ∈ v.asIdeal := fun v h => by
      rw [← hab v]
      show (q : 𝓞 B'.host.F) ∈ (w'.I.sel v).asIdeal.comap (algebraMap _ _)
      rw [Ideal.mem_comap, map_natCast]
      exact h
    have := pin.half v v' q hq (hmem v hqP) (hmem v' hqP')
    exact congrArg HeightOneSpectrum.asIdeal this
  have hfin : Wt'.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B' T'.pl
  have hconj : ∀ v ∈ Wt', B'.places.conj v ∈ Wt' :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f' ≤ B'.KsC := (GlobalTheory.Mem.Base.KsExact.lower w'.exact).2.2.1
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' hok hC hrange
  have hrange' : Set.range w'.I.xi = T'.set w'.I.C := by rw [hC]; exact hrange
  have hCK : ∀ x ∈ (w'.st Z').B.Ks, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = x := hKs
  have hCE : ∀ x : (w'.st Z').toD7.host.E, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = (w'.st Z').toD7.embE x :=
    fun x => hKs _ (B'.E_le_Ks x)
  have hmu : ∀ (L : Formalism.IndefR.Links.LevCh (w'.st Z').toD7 (TupU w'.I (usedOf w'.I T' Wt'))),
      L.Is (mu0F (X := (w'.st Z').B.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) → L.C = Top.Fr.at (w'.st Z') w'.I.C →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (x : (AE (w'.st Z').toD7)ˣ), infPart (w'.st Z').toD7 (x : AE (w'.st Z').toD7) = 1 →
        ∃ y : core'.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) := by
    intro L hL hLC i x hx
    have hLC' : L.C = Fr.at (w'.st Z') f' := hLC.trans (by rw [hC])
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ Formalism.L2.Pj.FO (w'.st Z').toD7 := by
      refine GlobalTheory.CoreExact.char_mem_of_values (w'.st Z').toD7 _ _ (hL.mu0 i) (Formalism.L2.Pj.FO (w'.st Z').toD7) ?_ ?_ x hx
      · rw [hLC', ← GlobalTheory.CoreExact.KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f'.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => ((w'.st Z').toD7.hc ((w'.st Z').toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (Formalism.L2.Pj.conj_mem_FO _ _ _) (Formalism.L2.Pj.conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨x₁, hx₁, hx₁'⟩ := (mem_FO_assembled_iff (w'.st Z') _).1 hmem
    obtain ⟨y, hy⟩ := hCK x₁ hx₁
    exact ⟨y, by rw [hy]; exact hx₁'.symm⟩
  exact GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices (w'.st Z') w'.px w'.I hX' T' Wt' core'.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hStdX hPos hCK hCE hmu

end GlobalTheory.Mem.R3.Rw

end
