import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMove
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.naturalAction_inverseFrame_undoes_move : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp), (X.Pj j).natAct (glInv X j (BOf fd j La)) (gmOf fd j La G) = G := by
  first | exact @GlobalTheory.TwV.DelA.natAct_glInv_gmOf | exact GlobalTheory.TwV.DelA.natAct_glInv_gmOf | (intros; apply GlobalTheory.TwV.DelA.natAct_glInv_gmOf <;> assumption)
