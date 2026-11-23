import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTuple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_left_restriction_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ (emb : UG (cA σ) (dbl (incM F X₁.J)) →* UG (cA σ) (dbl (incM F X.J))) (g₀ : UG (cA σ) (dbl (incM F X.J))),
        Continuous emb ∧ (∀ gd₁, IsDLevi H gd₁ (emb gd₁)) ∧
        (∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m → ∀ gd₁ : UG (cA σ) (dbl (incM F X₁.J)),
          gd₁.1.1 = Matrix.fromBlocks (mat g₁) 0 0 1 → (emb gd₁).1.1 = Matrix.fromBlocks (mat m) 0 0 1) ∧
        (∀ (p₁ : UG (cA σ) (dbl (incM F X₁.J))) (t₁ : GL (Fin n₁) (AE F E)),
          p₁.1.1 * (diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)) = (diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)) * t₁.1 →
          ∃ t : GL (Fin n) (AE F E), (emb p₁).1.1 * (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))) = (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))) * t.1 ∧
            Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det t₁) ∧
        ∀ z : Matrix (Fin d) (Fin n) (AE F E), ∃ z₁ : Matrix (Fin d) (Fin n₁) (AE F E), ∃ u ∈ isoD d H,
          z * (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))ᵀ = z₁ * ((diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)))ᵀ * (dblEmb H.ι)ᵀ + u := by
  first | exact @GlobalTheory.DoubledPlaneEmb.exists_dbl_emb | exact GlobalTheory.DoubledPlaneEmb.exists_dbl_emb | (intros; apply GlobalTheory.DoubledPlaneEmb.exists_dbl_emb <;> assumption)
