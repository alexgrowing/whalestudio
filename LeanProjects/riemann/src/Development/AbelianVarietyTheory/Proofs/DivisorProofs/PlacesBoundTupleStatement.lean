import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesBoundTuple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_left_restriction_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∀ et : ((((Fin n × Fin d) ⊕ (Fin n × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et Φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d))) →
        (∀ w : Matrix (Fin d) (Fin n₁ ⊕ Fin n₁) (AE F E), ∀ u ∈ isoD d H, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          et (dd.rho B.ψ (w * (dblEmb H.ι)ᵀ + u) Φ) = dd₁.rho B.ψ w (et Φ)) →
        (∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l ∘ₗ et ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        ∀ gd₁ md, IsDLevi H gd₁ md → ∃ c : ℂ, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et (omd md Φ) = c • omd₁ gd₁ (et Φ) := by
  first | exact @GlobalTheory.MixXDblInt.intertwine | exact GlobalTheory.MixXDblInt.intertwine | (intros; apply GlobalTheory.MixXDblInt.intertwine <;> assumption)
