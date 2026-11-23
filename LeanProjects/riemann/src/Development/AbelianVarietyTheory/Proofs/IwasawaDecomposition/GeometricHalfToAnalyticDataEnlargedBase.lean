import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsOfWeakCharacterisation
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtFW
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtOm
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtTies
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.geometricHalf_to_analyticData_enlargedBase : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
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
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R' → (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ x' ∈ (R'.FW i').WK, ∃ x ∈ (z.R.FW i).WK,
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) → CrdOver ι x x') →
        ∃ geo : GlobalTheory.RealGeo.GeoHalf core' R'.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo geo ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
          (∀ φ φ', HEq φ' φ → HEq ((R'.FW i').j (w'.st Z').toD7.what₂.embLL (geo.fw.e i' φ' : (R'.FW i').WK).1)
            ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)) ∧
          (HEq (geo.κ i').aP (z.geo.κ i).aP ∧ HEq (geo.κ i').aM (z.geo.κ i).aM ∧ (geo.κ i').n = (z.geo.κ i).n)) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((geo.fw.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k))) := by
  intro _ _ h3 _ _ _ _
  refine (GlobalTheory.Mem.R3.Rw.inGeo_stepW h3 Pinned).trans (Step.of_all fun K B' f' T' _ _ _ _ w' H => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1 _
  letI := alg'
  obtain ⟨hPins, hLev, -, -, -, hBrg, hEx', hRS⟩ := s1
  have hex : ∃ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := ⟨(by with_unfolding_all exact ((enlEmb hE.2.2.2) :)), (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))⟩
  refine hex.elim fun ι hι => ?_
  have hcomp : (w'.st Z').toD7.what₂.embLL.comp ι = (w.st Z).toD7.what₂.embLL := RingHom.ext hι
  have hfw := UpperTheory.Mem.GeoExt.exists_fw B B' f f' T T' w w' hE.1 Z hX Wt z Z' hX' {v | B'.places.resChar v ∈ T'.pl} core' alg' ha1 hc hL
    Xg tr R' hRS.1 hf hLev ι hι
  refine hfw.elim fun κ' hfw => hfw.elim fun v₀' hfw => hfw.elim fun fw' hfw => ?_
  have hκ := hfw.1
  have hv := hfw.2.1
  have he := hfw.2.2
  have hcrd : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
      ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k) :=
    fun i i' hi φ φ' hφ k k' hk => (congrArg _ ((he i i' hi φ φ' hφ).2 k k' hk)).trans (hι _)
  have hv0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) :=
    fun i i' hi => (hv i i' hi _).trans (congr_arg_heq (z.geo.v₀ i) hcomp)
  have hMW : GeoTies.MWOver z.R.toRealDat R'.toRealDat := fun i i' hi ι' hι' σ' => by
    have hcl := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι' hι').1 σ').1
    exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1, hcl.2.2.2.2.1, hcl.2.2.2.2.2.1, hcl.2.2.2.2.2.2.1⟩
  have hO := UpperTheory.Mem.GeoExt.exists_omOver z hE hf hpx hF.2.2.2 core' hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2 R' cG' hPins hLev hBrg hRS κ' v₀'
    (GlobalTheory.OneMapRefObj.tieIn_of_fwTie fw')
  refine hO.elim fun O' hO => ?_
  have hOP := hO.1
  have hOm := hO.2
  have t := UpperTheory.Mem.GeoExt.ties_enl w w' Z Z' hX hX' Wt {v | B'.places.resChar v ∈ T'.pl} z hE hpx core' alg' ha1 hc Xg tr R' cG' hPins hRS
    κ' hκ v₀' fw' hcrd hv0 O' hOP hOm hF.1 hH.unif hEx' hMW
  refine ⟨⟨κ', v₀', fw', t.1, O', hOP, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩, H Z' hX' _ core' alg' Xg tr R' cG' hPins hEx' _ _,
    fun i i' hi => ⟨hv0 i i' hi, fun φ φ' hφ => ?_, hκ i i' hi⟩, hcrd⟩
  have hj := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1
    (w'.st Z').toD7.what₂.embLL).2.2.2 _ _ (he i i' hi φ φ' hφ)
  exact hj.trans (congr_arg_heq (fun σ => (z.R.FW i).j σ (z.geo.fw.e i φ : (z.R.FW i).WK).1) hcomp)
