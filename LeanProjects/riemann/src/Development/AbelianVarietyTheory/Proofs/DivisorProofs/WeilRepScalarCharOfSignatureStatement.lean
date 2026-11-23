import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepScalarCharOfSignature
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_scalar_char_of_signature : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
      (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d), M.co.rho B.ψ γ (pure f M.vac) = c v γ • pure f M.vac) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ γ Ψ = c v γ • Ψ) →
        ∃ f₁ : SInf F (Fin n × Fin d), Ψ = pure f₁ M.vac := by
  first | exact @GlobalTheory.VacLine.vac_line | exact GlobalTheory.VacLine.vac_line | (intros; apply GlobalTheory.VacLine.vac_line <;> assumption)
