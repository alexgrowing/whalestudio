import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyFinal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankOneGramRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescalingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_final : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  first | exact @GlobalTheory.QColLaws.laws_resc | exact GlobalTheory.QColLaws.laws_resc | (intros; apply GlobalTheory.QColLaws.laws_resc <;> assumption)
