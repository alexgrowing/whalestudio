import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_restriction_pair_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
      IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∃ l ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        (∀ (y₁ y₂ : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          l (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H.x) + u * (incM F H.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H.x) + u * (incM F H.ι)ᵀ)) φ) = l φ) ∧
        (∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₁' ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), ∀ c : ℂ,
          e φ₁' = c • e φ₁ → l (boxFun φ₁' φ₂) = c * l (boxFun φ₁ φ₂)) ∧
        ∃ φ₁ ∈ schA F (Fin n × Fin d), ∃ φ₂ ∈ schA F (Fin n × Fin d), l (boxFun φ₁ φ₂) ≠ 0 := by
  first | exact @GlobalTheory.doubledEv_form | exact GlobalTheory.doubledEv_form | (intros; apply GlobalTheory.doubledEv_form <;> assumption)
