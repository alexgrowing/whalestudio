import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPreservingOperatorLocalStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_preserving_operator_local_structure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ A : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), A Φ ∈ schA F (Fin n × Fin d)) →
    (∀ (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
      ∀ Φ ∈ schA F (Fin n × Fin d), A (M.co.rho B.ψ w Φ) = M.co.rho B.ψ w (A Φ)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = M.vac v) → ∃ f₁ : SInf F (Fin n × Fin d), A (pure f φ) = pure f₁ φ := by
  first | exact @GlobalTheory.FinComm.commutant_pure | exact GlobalTheory.FinComm.commutant_pure | (intros; apply GlobalTheory.FinComm.commutant_pure <;> assumption)
