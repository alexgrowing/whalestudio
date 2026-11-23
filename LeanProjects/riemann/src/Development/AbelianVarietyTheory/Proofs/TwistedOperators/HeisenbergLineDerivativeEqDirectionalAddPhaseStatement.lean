import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeEqDirectionalAddPhase
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergLineDerivative_eq_directional_add_phase : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
    ActsD (evI F) (M.heisLine ψ u) g h → ∀ (y : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    h y = fderiv ℝ (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) y (fun i => evI F ((M.co.e u).1 i)) +
      (-(2 * Real.pi * Complex.I) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) : ℝ) : ℂ)) * g y := by
  first | exact @GlobalTheory.HeisDerivFormula.heisLine_deriv_eq | exact GlobalTheory.HeisDerivFormula.heisLine_deriv_eq | (intros; apply GlobalTheory.HeisDerivFormula.heisLine_deriv_eq <;> assumption)
