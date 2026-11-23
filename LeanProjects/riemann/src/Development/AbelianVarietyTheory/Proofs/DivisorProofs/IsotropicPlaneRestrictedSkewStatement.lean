import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneRestrictedSkew
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_plane_restricted_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J →
    Y₁.J.det ≠ 0 → ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m := by
  first | exact @GlobalTheory.LeviRatSkew.exists_rat_isLevi_one_skew | exact GlobalTheory.LeviRatSkew.exists_rat_isLevi_one_skew | (intros; apply GlobalTheory.LeviRatSkew.exists_rat_isLevi_one_skew <;> assumption)
