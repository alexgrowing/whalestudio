import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianOneByOneIsScalar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_scalar_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.sim_norm_le_one) | (exact GlobalTheory.StabFin.sim_norm_le_one) | (intros; apply GlobalTheory.StabFin.sim_norm_le_one  <;> assumption)
