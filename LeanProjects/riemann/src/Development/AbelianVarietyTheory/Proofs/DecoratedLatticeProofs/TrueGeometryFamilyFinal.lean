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

theorem GlobalTheory.QColLaws.laws_resc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _haT row col hr hc t F w₀ s hs hPin hQ
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hsh := ha.shape
  have hIs := GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col) hr
  have hweil := GlobalTheory.T.family_chars_weilOK_unramified W u hW.pk (a.fam row col) a.v hr hc (ha.tie row col).1
    (fun j h => ⟨hsh.pre.line.1, hsh.pre.tau j h⟩) t w₀ hQ
  exact GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling _ (a.fam row col).c a.v ((a.fam row col).t t) (GlobalTheory.QTw.resc w₀ s) hIs.1 (hIs.2 hc t) ha.vis hweil.1
    ⟨w₀, s, hs, ⟨F, hPin⟩, rfl⟩
