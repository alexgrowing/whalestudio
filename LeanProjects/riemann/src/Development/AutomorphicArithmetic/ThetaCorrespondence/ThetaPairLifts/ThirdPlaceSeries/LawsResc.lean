import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyFinal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyCharsStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.QColLaws.laws_resc_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _haT row col hr hc t F w₀ s hs hPin hQ
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hsh := ha.shape
  have hIs := _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col) hr
  have hweil := _root_.GlobalTheory.T.weilOK_of_rank_one_gram' W u hW.pk (a.fam row col) a.v hr hc (ha.tie row col).1
    (fun j h => ⟨hsh.pre.line.1, hsh.pre.tau j h⟩) t w₀ hQ
  exact GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling _ (a.fam row col).c a.v ((a.fam row col).t t) (GlobalTheory.QTw.resc w₀ s) hIs.1 (hIs.2 hc t) ha.vis hweil.1
    ⟨w₀, s, hs, ⟨F, hPin⟩, rfl⟩
end
