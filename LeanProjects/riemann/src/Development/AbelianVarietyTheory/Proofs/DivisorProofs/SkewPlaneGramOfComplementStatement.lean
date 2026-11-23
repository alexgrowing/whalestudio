import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneGramOfComplement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_plane_gram_of_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsSkew σ B r s → ∀ (H : Plane E n n₁) (J₁ : Matrix (Fin n₁) (Fin n₁) E), n = n₁ + 2 →
      form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
      (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = J₁ → J₁.det ≠ 0 →
      ∃ (Z : Spc F E n₁) (r₁ s₁ : ℕ), Z.J = J₁ ∧ Z.IsSkew σ B r₁ s₁ := by
  first | exact @GlobalTheory.PlaneCompl.complement_skew | exact GlobalTheory.PlaneCompl.complement_skew | (intros; apply GlobalTheory.PlaneCompl.complement_skew <;> assumption)
