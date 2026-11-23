import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLieDerivativeInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_lie_derivative_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ l : List (Multiplicative ℝ →* UA σ G.V.J), (∀ γ ∈ l, γ ∈ Lines σ G.V) →
      (l.map fun γ t => γ (Multiplicative.ofAdd t)).foldr (derL om) Φ ∈ GlobalTheory.ThK.PolData B G.M ∧
      (l ≠ [] → G.M.I om ((l.map fun γ t => γ (Multiplicative.ofAdd t)).foldr (derL om) Φ) = 0) := by
  first | exact @GlobalTheory.ThK.ZFinKill.kill | exact GlobalTheory.ThK.ZFinKill.kill | (intros; apply GlobalTheory.ThK.ZFinKill.kill <;> assumption)
