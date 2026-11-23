import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)), (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  first | exact @GlobalTheory.PenVol.relIndex_cosStab_eq_wt | exact GlobalTheory.PenVol.relIndex_cosStab_eq_wt | (intros; apply GlobalTheory.PenVol.relIndex_cosStab_eq_wt <;> assumption)
