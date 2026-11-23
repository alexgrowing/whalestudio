import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearizedFrobeniusInvertibleUpToPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I → ∀ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : N →ₛₗ[B.D.φ] P), SemiBC u → ∀ L : P →ₗ[B.A] N, (∀ x, L (u x) = Ψ x) → ∃ n : ℕ, (∀ y, L y = 0 → t ^ n • y = 0) ∧ ∀ x, ∃ y, L y = t ^ n • x := by
  first | exact @GlobalTheory.BSP.LinFrob.linFrob_inv_pow | exact GlobalTheory.BSP.LinFrob.linFrob_inv_pow | (intros; apply GlobalTheory.BSP.LinFrob.linFrob_inv_pow <;> assumption)
