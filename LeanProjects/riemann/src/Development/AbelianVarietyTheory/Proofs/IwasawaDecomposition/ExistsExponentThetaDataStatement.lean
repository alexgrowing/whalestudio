import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_theta_data : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂) (tw : NTw B.R B.host W.what₂ B.LL0 nd), IsEmpty tw.Tw → ∀ e : G0g nd → ↥B.LL0, ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) := by
  first | exact @GlobalTheory.MemN.exists_nexp_nth_of_isEmpty | exact GlobalTheory.MemN.exists_nexp_nth_of_isEmpty | (intros; apply GlobalTheory.MemN.exists_nexp_nth_of_isEmpty <;> assumption)
