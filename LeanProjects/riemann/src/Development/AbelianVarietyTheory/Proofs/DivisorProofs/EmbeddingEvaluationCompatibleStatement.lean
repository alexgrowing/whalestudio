import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingEvaluationCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_evaluation_compatible : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsLocPart M M₁ e ei ev → ∀ v : Pl F,
      (∀ u ∈ I, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
        Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → ev v φ₁ = ev v φ) ∧
      ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
        Acts (evFin F v) (M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ)) φ φ₁ →
        ∀ χ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁ → ev v φ₁ = χ₁ := by
  first | exact @GlobalTheory.EvLocPart.locPart_inv_heis | exact GlobalTheory.EvLocPart.locPart_inv_heis | (intros; apply GlobalTheory.EvLocPart.locPart_inv_heis <;> assumption)
