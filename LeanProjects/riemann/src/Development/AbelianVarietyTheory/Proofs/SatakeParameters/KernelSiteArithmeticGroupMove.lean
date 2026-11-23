import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfPStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry S hD hS c L γ hL
    | succ i => exact GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := GlobalTheory.T.movedDatum_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
