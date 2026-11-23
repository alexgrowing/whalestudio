import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHaarIntegralFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_haar_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ Φ ∈ schA F (Fin n × Fin d), Φ ≠ 0 →
      coef m om Φ 1 ≠ 0 ∧ (∀ g, ‖coef m om Φ g‖ ≤ ‖coef m om Φ 1‖) ∧ Measurable (coef m om Φ) := by
  first | exact @GlobalTheory.ThK.CoefBound.coef_ne_zero_bound_measurable | exact GlobalTheory.ThK.CoefBound.coef_ne_zero_bound_measurable | (intros; apply GlobalTheory.ThK.CoefBound.coef_ne_zero_bound_measurable <;> assumption)
