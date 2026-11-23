import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U → ∀ x : FinPt G X,
      GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  first | exact @GlobalTheory.RatMoveLat.latAt_rat | exact GlobalTheory.RatMoveLat.latAt_rat | (intros; apply GlobalTheory.RatMoveLat.latAt_rat <;> assumption)
