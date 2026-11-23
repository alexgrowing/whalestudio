import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionRestrictedProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_restricted_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) →
    (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    M.co.rho ψ u (pure f φ) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) (fun v => locOp v (M.co.rho ψ (partFin v u)) (φ v)) := by
  first | exact @GlobalTheory.HeisPure.rho_pure | exact GlobalTheory.HeisPure.rho_pure | (intros; apply GlobalTheory.HeisPure.rho_pure <;> assumption)
