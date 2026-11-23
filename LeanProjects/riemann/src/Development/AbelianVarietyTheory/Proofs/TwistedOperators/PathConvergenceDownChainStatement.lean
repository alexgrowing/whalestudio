import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.path_convergence_down_chain : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @GlobalTheory.FlipStart.column | exact GlobalTheory.FlipStart.column | (intros; apply GlobalTheory.FlipStart.column <;> assumption)
