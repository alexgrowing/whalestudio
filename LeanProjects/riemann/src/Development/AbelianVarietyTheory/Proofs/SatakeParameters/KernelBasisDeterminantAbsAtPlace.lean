import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormDetLatticeBasisEqDetIdealNormStatement
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.SatakeUnitDeterminantBasis

theorem detB : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  intro D Dx Tw E u μ O w T idl hp i hi c τ
  have hb := T.B_bas i hi c τ
  rw [O.dt_lat, hp.2.2.2.2]
  exact GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm D _ (E.lam w) τ _ _ _ _ (O.lattice_integral_coordinates i) hb.1 hb.2.1 hb.2.2

end GlobalTheory.SatakeUnitDeterminantBasis
