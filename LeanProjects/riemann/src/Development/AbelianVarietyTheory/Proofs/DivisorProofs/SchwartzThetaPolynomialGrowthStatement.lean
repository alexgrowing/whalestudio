import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_theta_polynomial_growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinDenom.exists_denominator_of_finite_component | exact GlobalTheory.FinDenom.exists_denominator_of_finite_component | (intros; apply GlobalTheory.FinDenom.exists_denominator_of_finite_component <;> assumption)
