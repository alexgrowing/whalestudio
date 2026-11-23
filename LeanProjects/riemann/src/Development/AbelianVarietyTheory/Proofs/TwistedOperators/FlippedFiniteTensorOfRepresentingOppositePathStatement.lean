import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (Φ : G.Datum) (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G (oppPath t D.R.m)), GlobalTheory.FlipRun.RepFin B ρ t (oppPath t D.R.m) τ (Tflip W B t Φ) → ∃ τ', GlobalTheory.RowClaim.IsFlipFin t B ρ Φ τ' ∧ GlobalTheory.FlipRun.tensE W (oppPath t D.R.m) Q τ = GlobalTheory.RowClaim.oppTens W t (Q.mapDomain GlobalTheory.FlipRun.toOpp) τ' := by
  first | exact @GlobalTheory.OppConv.flipFin_of_repFin | exact GlobalTheory.OppConv.flipFin_of_repFin | (intros; apply GlobalTheory.OppConv.flipFin_of_repFin <;> assumption)
