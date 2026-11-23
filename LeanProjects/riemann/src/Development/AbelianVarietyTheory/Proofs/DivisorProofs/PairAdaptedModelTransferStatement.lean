import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedModelTransfer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_model_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
      ∀ l₁ : ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ,
        (∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d))ᵀ) φ) = l₁ φ) →
      ∃ Λ : Submodule F ((Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
        (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧ Module.finrank F Λ = Fintype.card (Fin n × Fin d ⊕ Fin n × Fin d) ∧
        (∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          (l₁ ∘ₗ ed) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))) φ) = (l₁ ∘ₗ ed) φ) ∧
        ∃ (b : Module.Basis (Fin 2) F E) (w : Fin d × Fin 2 → (Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
          (∀ p q, (w p).1 ⬝ᵥ (w q).2 = (w q).1 ⬝ᵥ (w p).2) ∧
          (∀ c : Fin d × Fin 2 → F, (∀ v ∈ Λ, (∑ p, c p • w p).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ p, c p • w p).2) → c = 0) ∧
          ∀ u : Fin d → AE F E, dd.e (GlobalTheory.DblSiegelX.zs H u) =
            ∑ p, (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2 •
              ((fun i => algebraMap F (AF F) ((w p).1 i)), (fun i => algebraMap F (AF F) ((w p).2 i))) := by
  first | exact @GlobalTheory.DblSiegelLagr.exists_lagr | exact GlobalTheory.DblSiegelLagr.exists_lagr | (intros; apply GlobalTheory.DblSiegelLagr.exists_lagr <;> assumption)
