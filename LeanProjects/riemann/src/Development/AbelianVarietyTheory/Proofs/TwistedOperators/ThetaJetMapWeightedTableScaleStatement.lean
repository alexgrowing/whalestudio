import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScale
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetMap_weighted_table_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ) (P : Formalism.L2.DIV.Pol ℂ ι a), jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P = u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  first | exact @GlobalTheory.JetScale.jetMap_weight_scale | exact GlobalTheory.JetScale.jetMap_weight_scale | (intros; apply GlobalTheory.JetScale.jetMap_weight_scale <;> assumption)
