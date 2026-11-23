import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorFixesIntegralIndicator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_fixes_integral_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), ∀ᶠ v in cofinite,
      locOp v (M.co.rho ψ (partFin v u)) (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
        Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.VacFix.eventually_locOp_rho_indicator | exact GlobalTheory.VacFix.eventually_locOp_rho_indicator | (intros; apply GlobalTheory.VacFix.eventually_locOp_rho_indicator <;> assumption)
