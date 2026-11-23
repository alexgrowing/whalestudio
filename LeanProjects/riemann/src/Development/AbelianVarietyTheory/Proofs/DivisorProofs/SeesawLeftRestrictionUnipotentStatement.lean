import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_left_restriction_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
        (∀ z : Matrix (Fin d) (Fin n₁) (AE F E), ∀ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l (dd₁.rho B.ψ (z * ((diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)))ᵀ) φ) = l φ) →
        (∃ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l φ ≠ 0) →
        ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l ((partRₗ (conjLin e) ∘ₗ partLₗ e) Φ) ≠ 0 := by
  first | exact @GlobalTheory.DblEvNonvan.doubled_eval_nonvanishing | exact GlobalTheory.DblEvNonvan.doubled_eval_nonvanishing | (intros; apply GlobalTheory.DblEvNonvan.doubled_eval_nonvanishing <;> assumption)
