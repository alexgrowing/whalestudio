import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEHasTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsRealTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleWitnessZeroSectionEqStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitCfEqStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PgEqOfLinkedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSFinConjMatchStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPinTwArgsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerLastStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3Iff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3RealTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.TieOfLink
theorem tie_of_rpk_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) {x : TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y)
    (e : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) (hp : ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) :
    Nonempty b.Comparison₂ := by
  have key : ∀ z : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, z = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y → ∃ Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion z.B.Q, PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree z.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation z.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr := by
    rintro z rfl
    exact ⟨_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r, hpsi, h3, hp⟩
  obtain ⟨Rr, h⟩ := key _ e
  exact ⟨⟨Rr, h⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem nonempty_tie_of_wit (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y))
    (hloc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := _root_.GlobalTheory.T.recursion_local_row_condition_alt _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact _root_.GlobalTheory.Fc.TieOfLink.tie_of_rpk_alt b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩
theorem hasTie_of_linked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ => _root_.GlobalTheory.Fc.HasCompatibility := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((_root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq hL p).and (_root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq hL p)).and (_root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq hL p)).and (_root_.GlobalTheory.T.theta_level_conjugate_character_alt hL p)).and (_root_.GlobalTheory.T.local_level_character_pin_of_witness hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : _root_.GlobalTheory.Fc.HasCompatibility _ _ c b' := _root_.GlobalTheory.Fc.TieOfLink.nonempty_tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → _root_.GlobalTheory.Fc.HasCompatibility s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e
end GlobalTheory.Fc.TieOfLink
end
end
