import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_plane_compatible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      ∃ T : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) ∧
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (T Φ)) ∧
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = T Φ) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ∃ g : (Fin n → AE F E) → ℂ, (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable g μ ∧ ∫ y, g y ∂μ ≠ 0) ∧
            ∀ y, T (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) = g y • φ := by
  first | exact @GlobalTheory.MixedVec.exists_mixedEv | exact GlobalTheory.MixedVec.exists_mixedEv | (intros; apply GlobalTheory.MixedVec.exists_mixedEv <;> assumption)
