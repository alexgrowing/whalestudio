import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridPathCutAtSquareSwapRoute
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
theorem _root_.GlobalTheory.T.gridPath_cut_at_square_swap_route : ∀ {T : Type} (m : ℕ) (t : T) (i j : ℕ), i < m → j < m → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.SplitFlip.PassesThrough i j (GlobalTheory.FlipRun.edges p) → ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp ∧ GlobalTheory.FlipRun.OnGrid m t A ∧ GlobalTheory.FlipRun.OnGrid m t Bp ∧ GlobalTheory.FlipRun.OnGrid m t ((A.comp (routeBig t i j)).comp Bp) ∧ GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp) = GlobalTheory.SplitFlip.flipPath i j (GlobalTheory.FlipRun.edges p) := by
  first | exact @GlobalTheory.PathCut.cut_at_square | exact GlobalTheory.PathCut.cut_at_square | (intros; apply GlobalTheory.PathCut.cut_at_square <;> assumption)
