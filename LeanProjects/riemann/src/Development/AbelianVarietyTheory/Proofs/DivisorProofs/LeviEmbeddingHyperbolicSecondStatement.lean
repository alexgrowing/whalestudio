import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicSecond
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_hyperbolic_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∃ ι : GAd σ (c • Y₁.J.map σ) →* GAd σ (c • Y.J.map σ),
      (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 →
        ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 g₁ m ∧ m.1 = (ι g').1) ∧
      ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n₁) (Fin n₁) ℂ) (γ : ℝ → GAd σ (c • Y₁.J.map σ)),
        IsLineOf σ (c • Y₁.J.map σ) τ Z γ →
        IsLineOf σ (c • Y.J.map σ) τ (H.ι.map τ.1 * Z * (R.submatrix mid id).map τ.1) fun t => ι (γ t) := by
  first | exact @GlobalTheory.LeviEmbHC.leviEmb | exact GlobalTheory.LeviEmbHC.leviEmb | (intros; apply GlobalTheory.LeviEmbHC.leviEmb <;> assumption)
